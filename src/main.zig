const std = @import("std");
const log = std.log;
const print = std.debug.print;
const expect = std.testing.expect;
const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;
const ArrayListUnmanaged = std.ArrayListUnmanaged;

const problem = @import("problem.zig");
const constants = @import("constants.zig");
const utils = @import("utils.zig");
const solvers = @import("solvers.zig");

const parse_dimacs_cnf_file = problem.parse_dimacs_cnf_file;
const ProblemSpec = problem.ProblemSpec;

const SolverConfig = solvers.SolverConfig;
const CDCLSolver = solvers.CDCL;
const VariableDecisionPolicy = solvers.VariableDecisionPolicy;
const SolverResult = solvers.SolverResult;

const log_empty_line = utils.log_empty_line;
const testing = std.testing;

pub fn main() !void {
    const clap = @import("clap");

    const params = comptime [_]clap.Param(clap.Help){
        clap.parseParam("-h, --help               Display this help and exit.              ") catch unreachable,
        clap.parseParam("-f, --cnf-file <STR>...  Path to .cnf file in DIMACS format.") catch unreachable,
    };

    // Initalize our diagnostics, which can be used for reporting useful errors.
    // This is optional. You can also pass `.{}` to `clap.parse` if you don't
    // care about the extra information `Diagnostics` provides.
    var diag = clap.Diagnostic{};
    var args = clap.parse(clap.Help, &params, .{ .diagnostic = &diag }) catch |err| {
        // Report useful error and exit
        diag.report(std.io.getStdErr().writer(), err) catch {};
        return err;
    };
    defer args.deinit();

    if (args.flag("--help")) {
        print("tajza solver\n", .{});
        return clap.help(std.io.getStdErr().writer(), &params);
    }

    var file_path: []const u8 = undefined;
    for (args.options("--cnf-file")) |s|
        file_path = s;

    var gpa = std.heap.GeneralPurposeAllocator(.{ .safety = true }){};
    defer _ = gpa.deinit();

    const problem_spec: ProblemSpec = try parse_dimacs_cnf_file(gpa.allocator(), file_path);
    problem_spec.dump();

    const solver_config = SolverConfig{ .variable_decision_policy = VariableDecisionPolicy.mVSIDS, .vsids_decay_alpha = 0.1 };

    var cdcl_solver: CDCLSolver = undefined;
    try cdcl_solver.init(problem_spec, solver_config);
    defer cdcl_solver.deinit();

    const result = cdcl_solver.solve();
    print("result: {}\n", .{result});
    for (cdcl_solver.variable_assignments.items) |assignment, variable_id| {
        print("{} = {}\n", .{ variable_id, assignment });
        log.debug("{} = {}", .{ variable_id, assignment });
    }
}

test "parse dimacs cnf file" {
    testing.log_level = .debug;
    log_empty_line();

    var gpa = std.heap.GeneralPurposeAllocator(.{ .safety = true }){};
    defer _ = gpa.deinit();

    // const file_path = "aim-50-1_6-yes1-4.cnf";
    // const file_path = "hole6.cnf";
    // const file_path = "bf0432-007.cnf";
    const file_path = "benchmarks/uf250-097.cnf";
    // const file_path = "quinn.cnf";
    const problem_spec: ProblemSpec = try parse_dimacs_cnf_file(gpa.allocator(), file_path);
    problem_spec.dump();

    const solver_config = SolverConfig{ .variable_decision_policy = VariableDecisionPolicy.random };

    // var gpa2 = std.heap.GeneralPurposeAllocator(.{ .safety = true }){};
    // var base_allocator = gpa2.allocator();
    var cdcl_solver: CDCLSolver = undefined;
    try cdcl_solver.init(problem_spec, solver_config);
    defer cdcl_solver.deinit();

    try expect((try cdcl_solver.solve()) == SolverResult.sat);
    for (cdcl_solver.variable_assignments.items) |assignment, variable_id| {
        log.debug("{} = {}", .{ variable_id, assignment });
    }
}
