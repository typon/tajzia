const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const ArrayListUnmanaged = std.ArrayListUnmanaged;
const AutoArrayHashMap = std.AutoArrayHashMap;
const log = std.log;

const base = @import("base.zig");
const problem = @import("problem.zig");
const utils = @import("utils.zig");
const ArrayListUtils = utils.ArrayListUtils;
const ProblemSpec = problem.ProblemSpec;
const Literal = base.Literal;
const Polarity = base.Polarity;
const VariableAssignment = base.VariableAssignment;
const Clause = base.Clause;

var rng_factory = std.rand.DefaultPrng.init(0);

// Variable Decision Policies

// cVSIDS: The activities of variables occurring in the newest learnt clause are
// bumped up by 1, immediately after the clause is learnt. The activities of all
// variables are multiplied by a constant 0 < α < 1. The decay occurs after every i
// conflicts. We follow the policy used in recent solvers like MiniSAT and use i = 1.

// mVSIDS: The activities of all variables resolved during conflict analysis that
// lead to the learnt clause (including the variables in the learnt clause) are bumped
// up by 1. The activities of all variables are decayed as in cVSIDS.

pub const VariableDecisionPolicy = enum { random, mVSIDS };

pub const SolverResult = enum { sat, unsat, unknown };

// the unsat clause is also known as Kappa (in some notation)
const UnitPropagateResult = union(enum) { found_unsat_clause: usize, otherwise };

const AnalyzeClauseResult = enum { unit, unsat, sat, non_unit };

pub const SolverConfig = struct {
    variable_decision_policy: VariableDecisionPolicy,
    vsids_decay_alpha: f32,
};

pub const CDCL = struct {
    config: SolverConfig,
    main_arena_allocator: std.heap.ArenaAllocator,
    allocator: Allocator,
    problem_spec: ProblemSpec,
    variable_assignments: ArrayListUnmanaged(VariableAssignment),
    variable_decision_levels: ArrayListUnmanaged(i16),
    variable_antecedent_clause_ids: ArrayListUnmanaged(?usize),
    variable_activity: ArrayListUnmanaged(f32),
    num_assigned_variables: u32,
    rng: std.rand.Random,

    pub fn init(self: *CDCL, problem_spec: ProblemSpec, solver_config: SolverConfig) !void {

        // Handle random number generation
        const rng = rng_factory.random();

        self.config = solver_config;
        self.main_arena_allocator = std.heap.ArenaAllocator.init(std.heap.page_allocator);
        self.allocator = self.main_arena_allocator.allocator();
        self.problem_spec = problem_spec;
        self.variable_assignments = ArrayListUnmanaged(VariableAssignment){};
        self.variable_decision_levels = ArrayListUnmanaged(i16){};
        self.variable_antecedent_clause_ids = ArrayListUnmanaged(?usize){};
        self.variable_activity = ArrayListUnmanaged(f32){};
        self.num_assigned_variables = 0;
        self.rng = rng;

        try self.variable_assignments.appendNTimes(self.allocator, VariableAssignment.unassigned, problem_spec.num_variables);
        try self.variable_decision_levels.appendNTimes(self.allocator, -1, problem_spec.num_variables);
        try self.variable_antecedent_clause_ids.appendNTimes(self.allocator, null, problem_spec.num_variables);
        try self.variable_activity.appendNTimes(self.allocator, 0, problem_spec.num_variables);
    }

    pub fn deinit(self: *CDCL) void {
        self.problem_spec.arena.deinit();
        self.main_arena_allocator.deinit();
    }

    pub fn all_variables_assigned(self: *const CDCL) bool {
        return self.num_assigned_variables == self.problem_spec.num_variables;
    }

    fn decay_all_variables_activity(self: *CDCL) void {
        switch (self.config.variable_decision_policy) {
            VariableDecisionPolicy.mVSIDS => {
                for (self.variable_activity.items) |*activity| {
                    activity.* *= self.config.vsids_decay_alpha;
                }
            },
            else => {},
        }
    }

    fn decide_branching_variable_random_policy(self: *const CDCL) Literal {
        while (true) {
            const variable_id = self.rng.intRangeLessThan(u16, 0, @intCast(u16, self.variable_assignments.items.len));
            if (self.variable_assignments.items[variable_id] == VariableAssignment.unassigned) {
                const decided_polarity = self.rng.enumValue(Polarity);
                return Literal{ .id = variable_id, .polarity = decided_polarity };
            }
        }
    }

    fn decide_branching_variable_mVSIDS_policy(self: *const CDCL) Literal {
        const decided_polarity = self.rng.enumValue(Polarity);

        var max_activity_variable_id: ?usize = null;
        var max_activity: f32 = 0;
        for (self.variable_assignments.items) |variable_assignment, variable_id| {
            switch (variable_assignment) {
                VariableAssignment.unassigned => {
                    const activity = self.variable_activity.items[variable_id];
                    if (max_activity < activity) {
                        max_activity = activity;
                        max_activity_variable_id = variable_id;
                    } else if (max_activity_variable_id == null) {
                        max_activity_variable_id = variable_id;
                    }
                },
                else => {},
            }
        }
        return Literal{ .id = @intCast(u16, max_activity_variable_id.?), .polarity = decided_polarity };
    }

    fn decide_branching_variable(self: *const CDCL) Literal {
        var decided_variable: Literal = undefined;

        switch (self.config.variable_decision_policy) {
            VariableDecisionPolicy.random => {
                decided_variable = self.decide_branching_variable_random_policy();
            },
            VariableDecisionPolicy.mVSIDS => {
                decided_variable = self.decide_branching_variable_mVSIDS_policy();
            },
        }

        assert(self.variable_assignments.items[decided_variable.id] == VariableAssignment.unassigned);
        return decided_variable;
    }

    fn analyze_clause(self: *const CDCL, clause: *const ArrayListUnmanaged(Literal), unset_literal: *?Literal) AnalyzeClauseResult {
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

    fn assign_value_to_variable(self: *CDCL, unset_literal: Literal, decision_level: i16, clause_id: ?usize) void {
        self.variable_assignments.items[unset_literal.id] = if (unset_literal.polarity == Polarity.positive)
            VariableAssignment.true_
        else
            VariableAssignment.false_;

        self.variable_decision_levels.items[unset_literal.id] = decision_level;
        self.variable_antecedent_clause_ids.items[unset_literal.id] = clause_id;

        self.num_assigned_variables += 1;
    }

    fn unassign_variable(self: *CDCL, variable_id: u16) void {
        self.variable_assignments.items[variable_id] = VariableAssignment.unassigned;
        self.variable_decision_levels.items[variable_id] = -1;
        self.variable_antecedent_clause_ids.items[variable_id] = null;

        self.num_assigned_variables -= 1;
    }

    fn unit_propagate(self: *CDCL, decision_level: i16) UnitPropagateResult {
        var unit_clause_found = false;

        main_loop: while (true) {
            unit_clause_found = false;
            // Attempt to find a unit clause, and if one is found, set it's
            // only assigned literal to a value that causes the clause to become sat
            find_unit_clause_loop: for (self.problem_spec.clauses.items) |clause, clause_id| {
                var unset_literal: ?Literal = null;
                const clause_analysis = self.analyze_clause(&clause, &unset_literal);
                if (clause_analysis == AnalyzeClauseResult.unit) {
                    unit_clause_found = true;
                    self.assign_value_to_variable(unset_literal.?, decision_level, clause_id);
                    break :find_unit_clause_loop;
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

    fn resolve_conflict(self: *const CDCL, clause_a: Clause, clause_b: Clause, literal_used_to_resolve: Literal) !Clause {
        var literal_set = AutoArrayHashMap(Literal, void).init(self.allocator);

        for (clause_a.items) |literal| {
            if (literal.id == literal_used_to_resolve.id) {
                continue;
            }
            try literal_set.put(literal, {});
        }
        for (clause_b.items) |literal| {
            if (literal.id == literal_used_to_resolve.id) {
                continue;
            }
            try literal_set.put(literal, {});
        }

        var result = Clause{};
        for (literal_set.keys()) |literal| {
            try result.append(self.allocator, literal);
        }
        return result;
    }

    fn resolve_conflicts(self: *CDCL, decision_level: i16, conflict_clause_id: usize) !Clause {
        _ = self;
        _ = decision_level;
        _ = conflict_clause_id;

        // Visit all the literals of the learnt clause, examining each literal.
        // If the literal has an antecedent clause AND it was assigned at the current decision level,
        // then we can resolve the literal's antecedent clause with our currently-being-learned conflict clause.

        // However, if we only find a single literal at this decision level, then we have a Unique Implication Point (UIP)
        // In this case, we don't need to resolve conflict - we can simply use the initial conflict clause.

        var num_literals_at_this_decision_level: u32 = 0;
        var literal_used_to_resolve: ?Literal = null;
        var new_learnt_clause: Clause = try ArrayListUtils.clone(Clause, self.allocator, self.problem_spec.clauses.items[conflict_clause_id]);

        while (true) {
            num_literals_at_this_decision_level = 0;

            log.debug("length of clause: {}", .{new_learnt_clause.items.len});

            for (new_learnt_clause.items) |literal| {
                if (self.variable_decision_levels.items[literal.id] == decision_level) {
                    num_literals_at_this_decision_level += 1;
                    if (self.variable_antecedent_clause_ids.items[literal.id] != null) {
                        literal_used_to_resolve = literal;
                    }
                }
            }
            if (num_literals_at_this_decision_level == 1) {
                break;
            }

            const antecedent_clause_id_of_selected_literal: usize = self.variable_antecedent_clause_ids.items[literal_used_to_resolve.?.id].?;
            const antecedent_clause_of_selected_literal = self.problem_spec.clauses.items[antecedent_clause_id_of_selected_literal];

            // Handles VSIDS updates
            switch (self.config.variable_decision_policy) {
                VariableDecisionPolicy.mVSIDS => {
                    self.variable_activity.items[literal_used_to_resolve.?.id] += 1;
                },
                else => {},
            }

            new_learnt_clause = try self.resolve_conflict(new_learnt_clause, antecedent_clause_of_selected_literal, literal_used_to_resolve.?);
        }

        // Handles VSIDS updates
        switch (self.config.variable_decision_policy) {
            VariableDecisionPolicy.mVSIDS => {
                for (new_learnt_clause.items) |literal| {
                    self.variable_activity.items[literal.id] += 1;
                }
            },
            else => {},
        }

        return new_learnt_clause;
    }

    fn backtrack(self: *CDCL, decision_level: i16, new_learnt_clause: *const Clause) i16 {
        var backtracked_decision_level: i16 = 0;

        // Find the maximum decision level for any variable in the clause that's not the
        // decision level where the conflict happened.
        // This will be the new decision level we backtrack to.

        for (new_learnt_clause.items) |literal| {
            const decision_level_for_var = self.variable_decision_levels.items[literal.id];
            if (decision_level_for_var == decision_level) {
                continue;
            }
            backtracked_decision_level = std.math.max(backtracked_decision_level, decision_level_for_var);
        }

        // Any variabled assigned above the backtracked_decision_level is unassigned
        for (self.variable_decision_levels.items) |decision_level_for_var, variable_id| {
            if (decision_level_for_var > backtracked_decision_level) {
                self.unassign_variable(@intCast(u16, variable_id));
            }
        }

        return backtracked_decision_level;
    }

    fn conflict_analysis_and_backtrack(self: *CDCL, decision_level: i16, conflict_clause_id: usize) !i16 {
        _ = self;
        _ = conflict_clause_id;

        const new_learnt_clause: Clause = try self.resolve_conflicts(decision_level, conflict_clause_id);
        try self.problem_spec.clauses.append(self.allocator, new_learnt_clause);

        return self.backtrack(decision_level, &new_learnt_clause);
    }

    pub fn solve(self: *CDCL) !SolverResult {
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
            if (self.problem_spec.clauses.items.len % 10 == 0) {
                std.debug.print("num_assigned_variables: {}, num_clauses: {}, decision_level: {}\n", .{ self.num_assigned_variables, self.problem_spec.clauses.items.len, decision_level });
            }
            const decided_variable: Literal = self.decide_branching_variable();

            decision_level += 1;

            // Assign the decided polarity to the decided variable (these two concepts represented as a Literal)
            // Note the clause_id here is null because there is no antecedent clause.
            self.assign_value_to_variable(decided_variable, decision_level, null);

            // in an infinite loop, unit_propagate, find conflicts, backtrack until unsat or all
            // variables are assigned
            find_conflicts_and_learn_loop: while (true) {
                switch (self.unit_propagate(decision_level)) {
                    UnitPropagateResult.found_unsat_clause => |conflict_clause_id| {
                        // A conflict was found at the top decision level,
                        // entire formula is unsat.
                        if (decision_level == 0) {
                            return SolverResult.unsat;
                        }

                        self.decay_all_variables_activity();

                        // We are at a deeper decision level, thus we must
                        // learn new clauses from this conflict and backtrack to an earlier decision
                        // level
                        decision_level = try self.conflict_analysis_and_backtrack(decision_level, conflict_clause_id);
                    },
                    UnitPropagateResult.otherwise => {
                        // No conflicts found, breaking out of this loop and keep assigning more variables
                        break :find_conflicts_and_learn_loop;
                    },
                }
            }
        }
        return SolverResult.sat;
    }
};
