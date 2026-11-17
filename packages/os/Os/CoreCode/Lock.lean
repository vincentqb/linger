module

public import Os.CoreSpec

public section

/-! # Os.Lock — what a lock attempt does once it holds a lock

The kernel locks a file, not a path, and a holder may delete its lock file, so once `Os.Shell.flock`
holds a file's lock it asks whether the path still names that file and decides as `next` says:
it keeps the lock only of the file the path names, and locks the path's file again at most
`attempts` times in all. -/

namespace Os.Lock

/-- How many times `Os.Shell.flock` locks a file it then finds the path no longer names, as when
its holder deleted it meanwhile, before it answers that another process holds the lock. -/
def attempts : Nat := 8

/-- What attempt `attempt`, counting from 0, does once it holds a lock and learned whether the
path still names the file it holds (`named`): keep it when it does, and otherwise let it go and
try again, or, after the last attempt, answer that the lock is held. -/
def next (attempt : Nat) (named : Bool) : Next :=
  if named then .hold else if attempt + 1 < attempts then .again else .busy

end Os.Lock
