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

pub fn Pair(comptime First: type, comptime Second: type) type {
    return struct {
        first: First,
        second: Second,
    };
}

pub const ArrayListUtils = struct {
    pub fn clone(comptime T: type, allocator: Allocator, list: T) !T {
        var result = T{};
        try result.insertSlice(allocator, 0, list.items);
        return result;
    }

    pub fn max_element(comptime ElementType: type, list: anytype) usize {
        var result: ElementType = 0;
        var max_index: usize = 0;

        for (list.items) |item| {
            result = std.math.max(item, result);
            if (max_index >= list.items.len - 1) {
                break;
            }
            max_index += 1;
        }
        return max_index;
    }
};
