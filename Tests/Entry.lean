module

import Linger.Tools.Entry
public meta import Linger.Tools.Entry

/-! Concrete entry fixtures for help, explicit selection and complete argument lists. -/

namespace Linger.Tools.Entry.Tests

open Linger.Tools.Entry

-- Empty argv explains the CLI; selection is an explicit command.
#guard route [] == .session ["help"]

#guard route ["attach"] == .selector

#guard route ["a"] == .selector

-- The tmux group owns validation, including bare help and malformed operands.
#guard
  [[], ["ls"], ["select"], ["import"], ["export"], ["help"], ["--help"],
        ["ls", "/tmp/save with spaces"], ["select", "../older save"], ["import", "./-save"],
        ["export", "/tmp/世界"], ["select", ""], ["ls", "first", "second"], ["unknown", "", "世界"],
        ["tmux", "__daemon", "--"]].all
    fun rest => route ("tmux" :: rest) == .tmux rest

-- Retired top-level spellings reach the native session error with intact operands.
#guard
  [[], ["/tmp/save"], ["/tmp/save with spaces"], ["./-save"], [""], ["--help"], ["first", "second"],
        ["import", "__daemon", "", "世界"]].all
    fun rest => route ("import" :: rest) == .session ("import" :: rest)

#guard
  [[], ["/tmp/save"], ["/tmp/save with spaces"], ["./-save"], [""], ["--help"],
        ["first", "second"]].all
    fun rest => route ("export" :: rest) == .session ("export" :: rest)

-- Explicit commands, internal commands and malformed arguments remain untouched.
#guard
  [["ls"], ["ls", "--summary"], ["ls", "--porcelain", "-r", "alice@host"], ["list"], ["select"],
        ["status"], ["attach", "work@host", "/bin/sh", "-lc", "printf '%s\\n' 'hello world'"],
        ["__daemon", "work", "/tmp/a b", "/bin/sh", "-lc", "printf '%s' 'café 世界'"], ["__daemon"],
        ["--help"], ["-r", "host-a", "host-b"], ["unknown", "", "import", "--", "a b"], [""],
        ["Import", "save"], ["import-resurrect", "save"], ["Tmux", "ls"], ["tmux-select"],
        ["select", "work"], ["select", ""], ["select", "世界", "a b"]].all
    fun args => route args == .session args

end Linger.Tools.Entry.Tests
