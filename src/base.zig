const std = @import("std");
const ArrayListUnmanaged = std.ArrayListUnmanaged;

pub const Polarity = enum(u16) {
    positive,
    negative,
};

pub const VariableAssignment = enum(u8) {
    true_,
    false_,
    unassigned,
};

pub const Literal = packed struct {
    id: u16,
    polarity: Polarity,
};

pub const Clause = ArrayListUnmanaged(Literal);
