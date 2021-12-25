const std = @import("std");
const expect = std.testing.expect;
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
var rng_factory = std.rand.DefaultPrng.init(0);

fn add(a: i32, b: i32) i32 {
    return a + b;
}

const Polarity = enum(u16) {
    positive,
    negative,
};

const VariableAssignment = enum(u8) {
    true_,
    false_,
    unassigned,
};

const Literal = packed struct {
    id: u16,
    polarity: Polarity,
};

const VariableDecisionPolicy = enum { random };

const SolverResult = enum { sat, unsat, unknown };

const UnitPropagateResult = union(enum) { found_unsat_clause: usize, otherwise };

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

const SolverConfig = struct {
    variable_decision_policy: VariableDecisionPolicy,
};

const CDCLSolver = struct {
    config: SolverConfig,
    arena: std.heap.ArenaAllocator,
    allocator: Allocator,
    problem_spec: ProblemSpec,
    variable_assignments: ArrayListUnmanaged(VariableAssignment),
    variable_decision_levels: ArrayListUnmanaged(i16),
    variable_antecedent_clause_ids: ArrayListUnmanaged(?usize),
    num_assigned_variables: u32,
    rng: std.rand.Random,

    pub fn init(problem_spec: ProblemSpec, solver_config: SolverConfig) !CDCLSolver {
        var solver_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);

        // Handle random number generation
        const rng = rng_factory.random();

        var cdcl_solver = CDCLSolver{
            .config = solver_config,
            .arena = solver_arena,
            .allocator = solver_arena.allocator(),
            .problem_spec = problem_spec,
            .variable_assignments = ArrayListUnmanaged(VariableAssignment){},
            .variable_decision_levels = ArrayListUnmanaged(i16){},
            .variable_antecedent_clause_ids = ArrayListUnmanaged(?usize){},
            .num_assigned_variables = 0,
            .rng = rng,
        };

        try cdcl_solver.variable_assignments.appendNTimes(cdcl_solver.allocator, VariableAssignment.unassigned, problem_spec.num_variables);
        try cdcl_solver.variable_decision_levels.appendNTimes(cdcl_solver.allocator, -1, problem_spec.num_variables);
        try cdcl_solver.variable_antecedent_clause_ids.appendNTimes(cdcl_solver.allocator, null, problem_spec.num_variables);

        return cdcl_solver;
    }

    pub fn deinit(self: *CDCLSolver) void {
        self.problem_spec.arena.deinit();
        self.arena.deinit();
    }

    pub fn all_variables_assigned(self: *const CDCLSolver) bool {
        return self.num_assigned_variables == self.problem_spec.num_variables;
    }

    fn decide_branching_variable_random_policy(self: *const CDCLSolver) u16 {
        while (true) {
            const variable_id = self.rng.intRangeLessThan(u16, 0, @intCast(u16, self.variable_assignments.items.len));
            if (self.variable_assignments.items[variable_id] == VariableAssignment.unassigned) {
                return variable_id;
            }
        }
    }

    fn decide_branching_variable(self: *const CDCLSolver) u16 {
        switch (self.config.variable_decision_policy) {
            VariableDecisionPolicy.random => {
                return self.decide_branching_variable_random_policy();
            },
        }
    }

    fn analyze_clause(self: *const CDCLSolver, clause: *const ArrayListUnmanaged(Literal), unset_literal: *?Literal) AnalyzeClauseResult {
        var num_unassigned: u32 = 0;
        var num_false: u32 = 0;

        for (clause.items) |literal| {
            if (self.variable_assignments.items[literal.id] == VariableAssignment.unassigned) {
                num_unassigned += 1;
                unset_literal.* = literal;
            } else if ((self.variable_assignments.items[literal.id] == VariableAssignment.true_ and literal.polarity == Polarity.positive) or (self.variable_assignments.items[literal.id] == VariableAssignment.false_ and literal.polarity == Polarity.negative)) {
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

    fn assign_value_to_literal(self: *CDCLSolver, unset_literal: Literal, decision_level: i16, clause_id: usize) void {
        self.variable_assignments.items[unset_literal.id] = if (unset_literal.polarity == Polarity.positive)
            VariableAssignment.true_
        else
            VariableAssignment.false_;

        self.variable_decision_levels.items[unset_literal.id] = decision_level;
        self.variable_antecedent_clause_ids.items[unset_literal.id] = clause_id;

        self.num_assigned_variables += 1;
    }

    fn unit_propagate(self: *CDCLSolver, decision_level: i16) UnitPropagateResult {
        var unit_clause_found = false;

        main_loop: while (true) {
            // Attempt to find a unit clause, and if one is found, set it's
            // only assigned literal to a value that causes the clause to become sat
            for (self.problem_spec.clauses.items) |clause, clause_id| {
                var unset_literal: ?Literal = null;
                const clause_analysis = self.analyze_clause(&clause, &unset_literal);
                if (clause_analysis == AnalyzeClauseResult.unit) {
                    unit_clause_found = true;
                    self.assign_value_to_literal(unset_literal.?, decision_level, clause_id);
                    break :main_loop;
                } else if (clause_analysis == AnalyzeClauseResult.unsat) {
                    return UnitPropagateResult{ .found_unsat_clause = clause_id };
                }
            }
            if (!unit_clause_found) {
                break :main_loop;
            }
            // A unit clause was found, so keep going and finding more unit clauses
        }
        return UnitPropagateResult.otherwise;
    }

    pub fn solve(self: *CDCLSolver) SolverResult {
        _ = self;

        var decision_level: i16 = 0;

        // Do initial unit prop to find any conflicts immediately
        switch (self.unit_propagate(decision_level)) {
            UnitPropagateResult.found_unsat_clause => {
                return SolverResult.unsat;
            },
            UnitPropagateResult.otherwise => {},
        }

        while (!self.all_variables_assigned()) {
            const variable_id = self.decide_branching_variable();
            log.debug("variable: {}", .{variable_id});
            std.time.sleep(1000_000_000);
        }
        return SolverResult.unknown;
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

    const solver_config = SolverConfig{ .variable_decision_policy = VariableDecisionPolicy.random };

    var cdcl_solver = try CDCLSolver.init(problem_spec, solver_config);
    defer cdcl_solver.deinit();

    try expect(cdcl_solver.solve() == SolverResult.unknown);
}
