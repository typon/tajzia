const std = @import("std");
const sqlite = @import("sqlite");
const log = std.log;

pub const DBManager = struct {
    db: sqlite.Db,
    diags: sqlite.Diagnostics,

    pub fn init(self: *DBManager, dbfile: [:0]const u8) !void {
        self.db = try sqlite.Db.init(.{
            .mode = sqlite.Db.Mode{ .File = dbfile },
            .open_flags = .{
                .write = true,
                .create = true,
            },
            .threading_mode = .MultiThread,
        });

        self.diags = sqlite.Diagnostics{};

        try self.create_tables();
    }

    pub fn create_tables(self: *DBManager) !void {
        const commands = &[_][]const u8{
            \\
            \\          CREATE TABLE IF NOT EXISTS metadata (
            \\              version INTEGER NOT NULL,
            \\              num_variables INTEGER NOT NULL,
            \\              num_clauses INTEGER NOT NULL,
            \\              num_assigned_variables INTEGER NOT NULL
            \\          );
            ,
            \\          CREATE TABLE IF NOT EXISTS clauses (
            \\              id INTEGER NOT NULL,
            \\              clause BLOB NOT NULL
            \\          );
            ,
            \\          CREATE TABLE IF NOT EXISTS variable_assignments (
            \\              id INTEGER NOT NULL,
            \\              assignment INTEGER NOT NULL
            \\          );
            ,
            \\          CREATE TABLE IF NOT EXISTS variable_decision_levels (
            \\              id INTEGER NOT NULL,
            \\              decision_level INTEGER NOT NULL
            \\          );
            ,
            \\          CREATE TABLE IF NOT EXISTS variable_antecedent_clause_ids (
            \\              id INTEGER NOT NULL,
            \\              clause_id INTEGER
            \\          );
            ,
            \\          CREATE TABLE IF NOT EXISTS variable_activity (
            \\              id INTEGER NOT NULL,
            \\              activity INTEGER
            \\          );
            ,
            \\          CREATE TABLE IF NOT EXISTS variable_activity_backup (
            \\              id INTEGER NOT NULL,
            \\              activity INTEGER
            \\          );
        };

        inline for (commands) |command| {
            self.db.exec(command, .{ .diags = &self.diags }, .{}) catch |err| {
                log.err("unable to prepare statement, got error {s}. diagnostics: {s}", .{ err, self.diags });
                return err;
            };
        }
    }
};
