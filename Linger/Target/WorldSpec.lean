module

public import Linger.Target.CoreSpec
import SoftwareChallenge.Commands

public section

/-! # What remote commands assume of the world

A remote command runs through a transport, a command that runs linger elsewhere, which may be
any command, each reaching its host its own way: reaching it is the transport's, its keys, jumps,
latency and authentication included. `Transport.Delivers` says that a transport runs a `linger`
there with exactly the plain words after its own, or runs nothing. SSH hands those words, joined
by spaces, to the login shell of the remote account, which may be any shell, each with its own
quoting; `Shell.Literal` says that every shell passes `linger` and then plain words, one space
apart, to `linger` as exactly those words. -/

namespace Linger.Target.Remote.Shell

/-- SSH hands its command line to the login shell of the remote account, whichever shell that is,
and `split line` is the words the program that shell runs for `line` receives, its own name first.
A line that is `linger` and then plain words, one space apart, reaches `linger` as exactly those
words. A shell that changes, drops, joins or re-splits such a word, or passes `linger` any word
the line does not hold, falsifies it. -/
WorldClaim Literal (split : String → List String) :=
  ∀ words : List String,
    (∀ word ∈ words, plain word = true) →
      split (String.intercalate " " ("linger" :: words)) = "linger" :: words

end Linger.Target.Remote.Shell

namespace Linger.Target.Remote.Transport

/-- A transport is a host's commands that run linger there, and `deliver command words` is the
words the program `command` runs there receives when linger runs `command`'s words and then
`words`, its own name first, or `none` when it runs nothing, as when it cannot reach its host.
Each of the transport's commands, its query's and its attach's, hands the words on as they are,
as `docker exec` and `kubectl exec` do, or joined by spaces to the login shell of an account
there, as ssh does, which passes plain words on (`Shell.Literal`): either way `linger` and then
plain words reach a `linger` as exactly those words, or nothing runs. A command that changes,
drops, joins or re-splits such a word, or runs anything there but `linger` with them, falsifies
it. -/
WorldClaim Delivers (deliver : List String → List String → Option (List String))
  (transport : Transport) :=
  ∀ command ∈ [transport.query, transport.attach],
    ∀ words : List String,
      (∀ word ∈ words, Shell.plain word = true) →
        deliver command ("linger" :: words) = none ∨
          deliver command ("linger" :: words) = some ("linger" :: words)

end Linger.Target.Remote.Transport
