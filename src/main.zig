const std = @import("std");
const log = std.log;
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

test "parse dimacs cnf file" {
    testing.log_level = .debug;
    log_empty_line();

    var gpa = std.heap.GeneralPurposeAllocator(.{ .safety = true }){};
    defer _ = gpa.deinit();

    const allocator = gpa.allocator();

    // const file_path = "aim-50-1_6-yes1-4.cnf";
    const file_path = "quinn.cnf";
    const problem_spec: ProblemSpec = try parse_dimacs_cnf_file(allocator, file_path);
    problem_spec.dump();

    const solver_config = SolverConfig{ .variable_decision_policy = VariableDecisionPolicy.random };

    var cdcl_solver = try CDCLSolver.init(allocator, problem_spec, solver_config);
    defer cdcl_solver.deinit();

    try expect((try cdcl_solver.solve()) == SolverResult.sat);
    for (cdcl_solver.variable_assignments.items) |assignment, variable_id| {
        log.debug("{} = {}", .{ variable_id, assignment });
    }
}
