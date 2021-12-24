const std = @import("std");
const assert = std.debug.assert;
const log = std.log;
const print = @import("std").debug.print;
const constants = @import("constants.zig");
const utils = @import("utils.zig");
const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;
const ArrayListUnmanaged = std.ArrayListUnmanaged;

const log_empty_line = utils.log_empty_line;
const testing = std.testing;

fn add(a: i32, b: i32) i32 {
    return a + b;
}

const Polarity = enum(u16) {
    positive,
    negative,
};

const LiteralAssignment = enum(u8) {
    true_,
    false_,
    unassigned,
};

const Literal = packed struct {
    id: u16,
    polarity: Polarity,
};

const SolverResult = enum { sat, unsat, unknown };

const UnitPropagateResult = enum { found_unsat_clause, otherwise };
const AnalyzeClauseResult = enum { unit, unsat, sat, non_unit };
const ProblemSpec = struct {
    num_clauses: u32,
    num_variables: u32,
    arena: std.heap.ArenaAllocator,
    allocator: Allocator,
    clauses: ArrayListUnmanaged(ArrayListUnmanaged(Literal)),
    literal_frequency: ArrayList(Literal),

    pub fn dump(self: *const ProblemSpec) void {
        for (self.clauses.items) |clause| {
            for (clause.items) |variable| {
                if (variable.polarity == Polarity.positive) {
                    print("+", .{});
                } else {
                    print("-", .{});
                }
                print("{}, ", .{variable.id});
            }
            print("\n", .{});
        }
    }
};

const CDCLSolver = struct {
    arena: std.heap.ArenaAllocator,
    allocator: Allocator,
    problem_spec: ProblemSpec,
    literal_assignments: ArrayListUnmanaged(LiteralAssignment),
    literal_decision_levels: ArrayListUnmanaged(i16),

    pub fn init(problem_spec: ProblemSpec) !CDCLSolver {
        var solver_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
        var cdcl_solver = CDCLSolver{
            .arena = solver_arena,
            .allocator = solver_arena.allocator(),
            .problem_spec = problem_spec,
            .literal_assignments = ArrayListUnmanaged(LiteralAssignment){},
            .literal_decision_levels = ArrayListUnmanaged(i16){},
        };

        var i: u32 = 0;
        while (i < problem_spec.num_variables) : (i += 1) {
            try cdcl_solver.literal_assignments.append(cdcl_solver.allocator, LiteralAssignment.unassigned);
        }

        return cdcl_solver;
    }

    pub fn deinit(self: *CDCLSolver) void {
        self.problem_spec.arena.deinit();
        self.arena.deinit();
    }

    pub fn solve(self: *CDCLSolver) SolverResult {
        _ = self;

        _ = self.unit_propagate(0);

        return SolverResult.unknown;
    }

    fn analyze_clause(self: *const CDCLSolver, clause: *const ArrayListUnmanaged(Literal), unset_literal_id: *?u16) AnalyzeClauseResult {
        var num_unassigned: u32 = 0;
        var num_false: u32 = 0;

        for (clause.items) |literal| {
            if (self.literal_assignments.items[literal.id] == LiteralAssignment.unassigned) {
                num_unassigned += 1;
                unset_literal_id.* = literal.id;
            } else if ((self.literal_assignments.items[literal.id] == LiteralAssignment.true_ and literal.polarity == Polarity.positive) or (self.literal_assignments.items[literal.id] == LiteralAssignment.false_ and literal.polarity == Polarity.negative)) {
                // Return immediately if any literal in the clause is assigned true
                return AnalyzeClauseResult.sat;
            } else {
                num_false += 1;
            }
        }

        if (clause.items.len == num_false) {
            return AnalyzeClauseResult.unsat;
        } else if (num_unassigned == 1) {
            return AnalyzeClauseResult.unit;
        } else {
            return AnalyzeClauseResult.non_unit;
        }
    }

    fn unit_propagate(self: *CDCLSolver, decision_level: u32) UnitPropagateResult {
        const unit_clause_found = false;
        _ = decision_level;

        while (true) {
            for (self.problem_spec.clauses.items) |clause| {
                var unset_literal_id: ?u16 = null;
                print("{} \n", .{self.analyze_clause(&clause, &unset_literal_id)});
            }
            if (!unit_clause_found) {
                return UnitPropagateResult.otherwise;
            }
        }
        _ = self;
    }
};

const DimacsFileError = error{ MalformedProblemStatement, InvalidLiteral };

fn parse_dimacs_cnf_file(gpa: Allocator, file_path: []const u8) !ProblemSpec {
    const cur_dir = std.fs.cwd();
    const file_buffer = try cur_dir.readFileAlloc(gpa, file_path, constants.@"1 GB");
    defer gpa.free(file_buffer);

    log.debug("{s}:\n{s}", .{ file_path, file_buffer });

    var lines = std.mem.split(u8, file_buffer, "\n");
    var lineno: u32 = 0;

    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    const allocator = arena.allocator();
    var problem_spec: ProblemSpec = .{ .num_clauses = 0, .num_variables = 0, .arena = arena, .allocator = allocator, .clauses = ArrayListUnmanaged(ArrayListUnmanaged(Literal)){}, .literal_frequency = ArrayList(Literal).init(allocator) };

    while (lines.next()) |line| {
        log.debug("{s}\n", .{line});
        var tokens = std.mem.tokenize(u8, line, " ");
        if (tokens.buffer.len == 0) {
            continue;
        }
        const first_char: u8 = tokens.buffer[0];

        // Skip over any comments
        if (first_char == 'c') {
            continue;
        }

        if (lineno == 0) {
            const first_token = tokens.next() orelse return DimacsFileError.MalformedProblemStatement;
            assert(first_token[0] == 'p');

            const second_token = tokens.next() orelse return DimacsFileError.MalformedProblemStatement;
            assert(std.mem.eql(u8, second_token, "cnf"));

            const num_variables = tokens.next() orelse return DimacsFileError.MalformedProblemStatement;
            problem_spec.num_variables = try std.fmt.parseInt(u32, num_variables, 0);

            const num_clauses = tokens.next() orelse return DimacsFileError.MalformedProblemStatement;
            problem_spec.num_clauses = try std.fmt.parseInt(u32, num_clauses, 0);
        } else {
            log.debug("lineno: {}\n", .{lineno});

            var literals = ArrayListUnmanaged(Literal){};
            while (tokens.next()) |token| {
                var literal = try std.fmt.parseInt(i32, token, 0);
                if (literal == 0) {
                    break;
                }
                // Literals are stored as 0 indexed in the solver
                var literal_symbol: u16 = @intCast(u16, (try std.math.absInt(literal)) - @intCast(i32, 1));
                var polarity = Polarity.positive;
                if (literal < 0) {
                    polarity = Polarity.negative;
                }
                try literals.append(problem_spec.allocator, Literal{ .id = literal_symbol, .polarity = polarity });
            }
            try problem_spec.clauses.append(problem_spec.allocator, literals);
        }

        lineno += 1;
    }

    return problem_spec;
}

test "parse dimacs cnf file" {
    testing.log_level = .debug;
    log_empty_line();

    var gpa = std.heap.GeneralPurposeAllocator(.{ .safety = true }){};
    defer _ = gpa.deinit();

    const allocator = gpa.allocator();

    const file_path = "test.cnf";
    const problem_spec: ProblemSpec = try parse_dimacs_cnf_file(allocator, file_path);

    problem_spec.dump();

    // var cdcl_solver: CDCLSolver = .{ .arena = solver_arena, .allocator = solver_arena.allocator(), .problem_spec = problem_spec, .decision_level = 0 };
    // defer _ = cdcl_solver.problem_spec.arena.deinit();
    // defer _ = cdcl_solver.arena.deinit();
    var cdcl_solver = try CDCLSolver.init(problem_spec);
    defer cdcl_solver.deinit();

    _ = cdcl_solver.solve();
}
