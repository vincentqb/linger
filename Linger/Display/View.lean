module

public import Linger.Display.Spec
import Linger.Display.Status

public section

/-! # Linger.Display.View — what a view of many sessions shows first, and how it sums up the rest

**Nothing that needs you is hidden, and every count adds up.** A view lists the statuses that
ask for someone first (`sort_attention_first`), keeps the listing's order within a status
(`sort_stable`) and loses no row (`sort_perm`). Its header counts every row and, among them,
those that ask for someone, whatever a query shows (`headerParts`). The rows a window cannot
show are summed up by groups of names, with exact counts that add up to the rows left out
(`groups_count`, `groups_sum`). A group is named by the start of its members' names, so typing
its name keeps all of them (`stem_prefix`), and names are cut at the depth that splits the rows
most evenly into groups few enough to name, and fewer than the rows (`chooseDepth_best`). -/

namespace Linger.Display.View

open Linger.Display.Status (Status)

/-- The order a view shows statuses in, those that ask for someone first: `? ! ⣿ ✓ ⣷ ⣀ ~`. -/
def order : List Status := [.unknown, .exitedBad, .wantsYou, .exitedOk, .working, .idle, .resumable]

/-- Rows in `order` of their status, each status's rows in listing order. -/
def sort {α : Type} (status : α → Status) (rows : List α) : List α :=
  order.flatMap fun st => rows.filter (status · == st)

/-- The parts of a view's header, which a view joins with ` · `: `linger`, what it lists
(`labels`), how many rows it lists, and the attention counts over all of them when there are
any (`Status.summary`). -/
def headerParts (labels : List String) (statuses : List Status) : List String :=
  "linger" :: labels ++
    toString statuses.length ::
      if (Status.summary statuses).isEmpty then [] else [Status.summary statuses]

/-- Whether `c` separates the parts of a session name: `-`, `_` or `.`. -/
def separator (c : Char) : Bool := c == '-' || c == '_' || c == '.'

/-- The characters of a target before its `depth`-th separator or its host's `@`, or all of
them when it has fewer separators. -/
def stemChars : Nat → List Char → List Char
  | _, [] => []
  | depth, c :: cs =>
    if c == '@' then []
    else
      if separator c then if depth ≤ 1 then [] else c :: stemChars (depth - 1) cs
      else c :: stemChars depth cs

/-- A target's group at `depth`: its name before its `depth`-th separator. -/
def stem (depth : Nat) (target : String) : String := String.ofList (stemChars depth target.toList)

/-- Each distinct key in order of first appearance, with how many times it occurs. -/
def groups : List String → List (String × Nat)
  | [] => []
  | k :: ks => (k, ks.count k + 1) :: groups (ks.filter (· != k))
termination_by keys => keys.length
decreasing_by
  have hle := List.length_filter_le (· != k) ks
  simp only [List.length_cons, List.unattach_filter, List.unattach_attach] at hle ⊢
  omega

/-- The most groups a summary names. -/
def maxGroups : Nat := 6

/-- The depths a summary may cut names at. -/
def depths : List Nat := [1, 2, 3]

/-- How unevenly `depth` splits `targets`: the size of its largest group. -/
def largest (depth : Nat) (targets : List String) : Nat :=
  ((groups (targets.map (stem depth))).map (·.2)).foldl max 0

/-- Whether grouping `targets` at `depth` helps a summary: there are few enough groups to name,
and fewer groups than targets, so a group says more than listing its targets would. -/
def useful (depth : Nat) (targets : List String) : Bool :=
  let count := (groups (targets.map (stem depth))).length
  count ≤ maxGroups && count < targets.length

/-- `chooseDepth`'s look at one more depth: a useful depth replaces the best so far when its
largest group is no larger, or when there is none so far. Depths come shallow first, so a tie
goes to the deeper depth, whose names say more. -/
def better (targets : List String) (best : Option Nat) (depth : Nat) : Option Nat :=
  if useful depth targets then
    match best with
    | some b => if largest depth targets ≤ largest b targets then some depth else best
    | none => some depth
  else best

/-- The useful depth that splits `targets` most evenly, the deeper on a tie; `none` when no depth
is useful. -/
def chooseDepth (targets : List String) : Option Nat := depths.foldl (better targets) none

/-- What a view says of the rows its window leaves out: how many, and their groups at the depth
`chooseDepth` picks, or no groups when it picks none. -/
def hidden (targets : List String) : Nat × List (String × Nat) :=
  (targets.length,
    ((chooseDepth targets).map fun depth => groups (targets.map (stem depth))).getD [])

end Linger.Display.View
