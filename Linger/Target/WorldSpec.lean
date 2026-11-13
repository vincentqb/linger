module

public import Linger.Target.CoreSpec
import SoftwareChallenge.Commands

public section

/-! # What remote commands assume of the world

SSH hands a remote command line to the login shell of the remote account, which may be any shell,
each with its own quoting; the world claim `Shell.Literal` says that every shell passes `linger`
and then plain words, one space apart, to `linger` as exactly those words. -/

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
