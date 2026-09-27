module

import Tools.Entry
public meta import Tools.Entry

/-! Concrete entry fixtures for help, explicit selection and complete argument lists. -/

namespace Tools.Entry.Tests

open Tools.Entry

-- Empty argv explains the CLI; selection is an explicit command.
#guard route [] == .session ["help"]

#guard route ["select"] == .selector

-- Import owns validation of its remaining arguments, including invalid operands.
#guard
  [[], ["/tmp/save"], ["/tmp/save with spaces"], ["./-save"], [""], ["--help"], ["first", "second"],
        ["import", "__daemon", "", "世界"]].all
    fun rest => route ("import" :: rest) == .importSave rest

-- Explicit commands, internal commands and malformed arguments remain untouched.
#guard
  [["ls"], ["ls", "--porcelain", "-r", "alice@host"], ["list"],
        ["attach", "work@host", "/bin/sh", "-lc", "printf '%s\\n' 'hello world'"],
        ["__daemon", "work", "/tmp/a b", "/bin/sh", "-lc", "printf '%s' 'café 世界'"], ["__daemon"],
        ["--help"], ["-r", "host-a", "host-b"], ["unknown", "", "import", "--", "a b"], [""],
        ["Import", "save"], ["import-resurrect", "save"], ["select", "work"], ["select", ""],
        ["select", "世界", "a b"]].all
    fun args => route args == .session args

end Tools.Entry.Tests
