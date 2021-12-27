const std = @import("std");
const log = std.log;
const print = @import("std").debug.print;
const Allocator = std.mem.Allocator;
const ArrayListUnmanaged = std.ArrayListUnmanaged;

pub fn log_empty_line() void {
    if (log.level == log.Level.debug) {
        print("\n", .{});
    }
}

pub const ArrayListUtils = struct {
    pub fn clone(comptime T: type, allocator: Allocator, list: T) !T {
        var result = T{};
        try result.insertSlice(allocator, 0, list.items);
        return result;
    }
};
