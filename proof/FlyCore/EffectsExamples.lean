import FlyCore.Effects

/-!
The semantics computes what the language means: these run in the kernel.
-/

namespace FlyCore.Effects.Examples

open Expr

/-- `handle { Ask.ask(1) + Ask.ask(2) } with Ask { ask(n) resumes k => k(n + 100) }`: the body is
resumed twice, the handler staying in force for the second operation (deep). -/
def deep : Expr :=
  .handle (.add (.perform 0 (.lit 1)) (.perform 0 (.lit 2))) 0 "n"
    (.add (.var "n") (.lit 100))

example : (eval [] 20 0 [] [] deep).1 = .val (.int 203) := by decide

/-- An abortive arm: the `handle`'s value is the arm's, and the rest of the body never runs. -/
def aborts : Expr :=
  .handleAbort (.add (.perform 0 (.lit 5)) (.lit 1000)) 0 "n" (.add (.var "n") (.lit 1))

example : (eval [] 20 0 [] [] aborts).1 = .val (.int 6) := by decide

/-- An arm runs where its `handle` is: a failure it raises goes to the `try` around the `handle`,
not to the one the body is inside. -/
def lexical : Expr :=
  .try_
    (.handle
      (.try_ (.perform 0 (.lit 1)) "e" (.lit 111))
      0 "n" (.throw_ (.lit 7)))
    "e" (.add (.var "e") (.lit 1))

example : (eval [] 20 0 [] [] lexical).1 = .val (.int 8) := by decide

end FlyCore.Effects.Examples
