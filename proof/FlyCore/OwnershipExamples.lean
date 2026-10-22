import FlyCore.Ownership

/-!
The semantics computes what the language means, in the kernel: a program that lends and moves
ends with every cell freed, and the aliasing the types forbid is a use after free.
-/

namespace FlyCore.Ownership.Examples

open Expr Place

def empty : Store := { mem := fun _ => none, next := 0 }

/-- `function add(b: Box<int>, r: mut Box<int>): int { *r = *r + *b; *r }` -/
def addInto : Fn :=
  { owns := [("b", .box .int)], refs := [("r", .mut, .box .int)], ret := .int,
    body := .seq (.write (deref (var "r")) (.add (.read (deref (var "r"))) (.read (deref (var "b")))))
      (.read (deref (var "r"))) }

/-- `let x = Box.new(1); let y = Box.new(41); addInto(y, mut x)`: 42, and nothing left allocated. -/
def lends : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1))
    (.let_ "y" (.box .int) (.new (.lit 41))
      (.call 0 [.move "y"] [(.mut, var "x")]))

example : (eval [addInto] 20 empty [] lends).1 = .val (.int 42) := by decide
example : ∀ l < (eval [addInto] 20 empty [] lends).2.next,
    (eval [addInto] 20 empty [] lends).2.mem l = none := by decide

/-- `function g(a: mut Box<int>, c: int (readonly)): int { a = Box.new(7); c }`, called with
`mut x` and `readonly *x`: the assignment frees the cell `c` borrows. -/
def clobber : Fn :=
  { owns := [], refs := [("a", .mut, .box .int), ("c", .ro, .int)], ret := .int,
    body := .seq (.assign (var "a") (.box .int) (.new (.lit 7))) (.read (var "c")) }

def aliased : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1)) (.call 0 [] [(.mut, var "x"), (.ro, deref (var "x"))])

example : (eval [clobber] 20 empty [] aliased).1 = .stuck := by decide

end FlyCore.Ownership.Examples
