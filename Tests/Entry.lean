module

import Tools.Entry
public meta import Tools.Entry

/-! Concrete entry fixtures across every stream mode and complete argument lists. -/

namespace Tools.Entry.Tests

open Tools.Entry

-- Only a bare invocation with both streams attached to terminals selects.
#guard route [] false false == .session []

#guard route [] false true == .session []

#guard route [] true false == .session []

#guard route [] true true == .selector

-- Import owns validation of its remaining arguments, including invalid operands.
#guard
  [(false, false), (false, true), (true, false), (true, true)].all fun (stdinTty, stdoutTty) =>
    [[], ["/tmp/save"], ["/tmp/save with spaces"], ["./-save"], [""], ["--help"],
          ["first", "second"], ["import", "__daemon", "", "世界"]].all
      fun rest => route ("import" :: rest) stdinTty stdoutTty == .importSave rest

-- Explicit commands, internal commands and malformed arguments remain untouched.
#guard
  [(false, false), (false, true), (true, false), (true, true)].all fun (stdinTty, stdoutTty) =>
    [["ls"], ["ls", "--porcelain", "-r", "alice@host"], ["list"],
          ["attach", "work@host", "/bin/sh", "-lc", "printf '%s\\n' 'hello world'"],
          ["__daemon", "work", "/tmp/a b", "/bin/sh", "-lc", "printf '%s' 'café 世界'"], ["__daemon"],
          ["--help"], ["-r", "host-a", "host-b"], ["unknown", "", "import", "--", "a b"], [""],
          ["Import", "save"], ["import-resurrect", "save"]].all
      fun args => route args stdinTty stdoutTty == .session args

end Tools.Entry.Tests
