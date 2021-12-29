const std = @import("std");
const log = std.log;
const assert = std.debug.assert;
const print = @import("std").debug.print;
const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;
const ArrayListUnmanaged = std.ArrayListUnmanaged;

const base = @import("base.zig");
const constants = @import("constants.zig");
const Literal = base.Literal;
const Polarity = base.Polarity;
const Clause = base.Clause;

const DimacsFileError = error{ MalformedProblemStatement, InvalidLiteral };

pub const ProblemSpec = struct {
    num_clauses: u32,
    num_variables: u32,
    arena: std.heap.ArenaAllocator,
    allocator: Allocator,
    clauses: ArrayListUnmanaged(Clause),
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

pub fn parse_dimacs_cnf_file(gpa: Allocator, file_path: []const u8) !ProblemSpec {
    const cur_dir = std.fs.cwd();
    const file_buffer = try cur_dir.readFileAlloc(gpa, file_path, constants.@"1 GB");
    defer gpa.free(file_buffer);

    // log.debug("{s}:\n{s}", .{ file_path, file_buffer });

    var lines = std.mem.split(u8, file_buffer, "\n");

    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    const allocator = arena.allocator();
    var problem_spec: ProblemSpec = .{ .num_clauses = 0, .num_variables = 0, .arena = arena, .allocator = allocator, .clauses = ArrayListUnmanaged(Clause){}, .literal_frequency = ArrayList(Literal).init(allocator) };

    var lineno: u32 = 0;
    while (lines.next()) |line| {
        const mutable_line = try allocator.alloc(u8, line.len);
        defer allocator.free(mutable_line);
        std.mem.copy(u8, mutable_line, line);

        std.mem.replaceScalar(u8, mutable_line, '\t', ' ');

        var tokens = std.mem.tokenize(u8, mutable_line, " ");
        if (tokens.buffer.len == 0) {
            continue;
        }
        const first_char: u8 = tokens.buffer[0];

        // Skip over any comments
        if (first_char == 'c') {
            continue;
        }

        if (first_char == '%') {
            break;
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
