import FlyCore.OwnershipSound

/-!
The semantics computes what the language means, in the kernel: a program that lends and moves
ends with every cell freed, handlers resume and unwind dropping what the scopes they leave own,
and the aliasing the types forbid is a use after free.
-/

namespace FlyCore.Ownership.Examples

open Expr Place

def empty : Store := { mem := fun _ => none, next := 0 }

/-- `function add(b: Box<int>, r: mut Box<int>): int { *r = *r + *b; *r }` -/
def addInto : Fn :=
  { owns := [("b", .box .int)], refs := [("r", .mut, .box .int)], ret := .int, row := [],
    body := .seq (.write (deref (var "r")) (.add (.read (deref (var "r"))) (.read (deref (var "b")))))
      (.read (deref (var "r"))) }

/-- `let x = Box.new(1); let y = Box.new(41); addInto(y, mut x)`: 42, and nothing left allocated. -/
def lends : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1))
    (.let_ "y" (.box .int) (.new (.lit 41))
      (.call 0 [.move "y"] [(.mut, var "x")]))

example : (eval [addInto] [] 20 [] empty [] lends).1 = .val (.int 42) := by decide
example : ∀ l < (eval [addInto] [] 20 [] empty [] lends).2.next,
    (eval [addInto] [] 20 [] empty [] lends).2.mem l = none := by decide

/-- `function g(a: mut Box<int>, c: int (readonly)): int { a = Box.new(7); c }`, called with
`mut x` and `readonly *x`: the assignment frees the cell `c` borrows. -/
def clobber : Fn :=
  { owns := [], refs := [("a", .mut, .box .int), ("c", .ro, .int)], ret := .int, row := [],
    body := .seq (.assign (var "a") (.box .int) (.new (.lit 7))) (.read (var "c")) }

def aliased : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1)) (.call 0 [] [(.mut, var "x"), (.ro, deref (var "x"))])

example : (eval [clobber] [] 20 [] empty [] aliased).1 = .stuck := by decide

/-! The types accept `lends`, so `program_ok` covers it; they reject `aliased`. -/

theorem addInto_ok : FnsOk [addInto] [] := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  refine ⟨by decide, _, .seq (.write (.add (.read (.deref (.ref (m := .mut) rfl))) (.read (.deref (.own rfl))))
    (.deref (.ref (m := .mut) rfl))) (.read (.deref (.ref (m := .mut) rfl)))⟩

theorem lends_typed : Typed [addInto] [] [] lends .int [] [.fail] := by
  have hc : Typed [addInto] [] [("y", .own (.box .int) true), ("x", .own (.box .int) true)]
      (.call 0 [.move "y"] [(.mut, var "x")]) .int
      [("y", .own (.box .int) false), ("x", .own (.box .int) true)] [.fail] := by
    have := Typed.call (F := [addInto]) (O := []) (Γ := [("y", .own (.box .int) true), ("x", .own (.box .int) true)])
      (f := 0) (d := addInto) (ys := [(.mut, "x")]) (r := [.fail]) rfl (by simp [addInto])
      (.cons (.move (x := "y") rfl) .nil) (.cons (.own (by simp [lookup, setSlot])) (fun _ => rfl) .nil)
      (by simp [Exclusive])
    simpa [setSlot, addInto] using this
  exact .let_ rfl (.new .lit) (.let_ rfl (.new .lit) hc)

example : ∀ n, match eval [addInto] [] n [.abort .fail 0] .empty [] lends with
    | (.stuck, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok addInto_ok lends_typed

/-- `let x = Box.new(1); try { let y = Box.new(2); throw *y } catch (e) { e + *x }`: the failure
leaves `y`'s scope, which drops it, and the handler sees `x`; 3, and nothing left allocated. -/
def unwinds : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1))
    (.try_ (.let_ "y" (.box .int) (.new (.lit 2)) (.throw_ (.read (deref (var "y"))))) "e"
      (.add (.read (var "e")) (.read (deref (var "x")))))

example : (eval [] [] 20 [] .empty [] unwinds).1 = .val (.int 3) := by decide
example : ∀ l < (eval [] [] 20 [] .empty [] unwinds).2.next, (eval [] [] 20 [] .empty [] unwinds).2.mem l = none := by
  decide

theorem unwinds_typed : Typed [] [] [] unwinds .int [] [] :=
  .let_ rfl (.new .lit) (.try_ rfl (.let_ rfl (.new .lit) (.throw_ (.read (.deref (.own rfl))) (by simp)))
    (.add (.read (.own rfl)) (.read (.deref (.own rfl)))))

theorem aliased_rejected : ¬ Typed [clobber] O [] aliased τ Γ' r := by
  intro h
  cases h with
  | let_ _ _ hb =>
    cases hb with
    | call hf _ _ hl hx =>
      simp at hf
      subst hf
      cases hl with
      | cons hp _ hl =>
        cases hl with
        | cons hp' _ hl =>
          cases hl
          cases hp
          · cases hp' with
            | deref hq => cases hq <;> simp_all [Exclusive]
          · simp_all [lookup]

/-! Effects and ownership together. -/

/-- `Ask`, whose operation takes nothing and gives an integer; and `Stop`, whose operation takes an
integer, for a handler that ends its `handle`. -/
def ops : List Op := [{ owns := [], refs := [], ret := .int }, { owns := [.int], refs := [], ret := .int }]

/-- `let base = Box.new(40); handle { Ask.ask() + *base } with Ask { ask() resumes k => k(*b + 1) }`,
the arm lent `*base` as `b`: the body reads `base` while the arm may, and neither may change it. 81,
and nothing left allocated. -/
def asks : Expr :=
  .let_ "base" (.box .int) (.new (.lit 40))
    (.handle (.add (.perform 0 [] []) (.read (deref (var "base")))) 0 [("b", deref (var "base"))] [] []
      (.add (.read (var "b")) (.lit 1)))

example : (eval [] ops 20 [] .empty [] asks).1 = .val (.int 81) := by decide
example : ∀ l < (eval [] ops 20 [] .empty [] asks).2.next, (eval [] ops 20 [] .empty [] asks).2.mem l = none := by
  decide

theorem asks_typed : Typed [] ops [] asks .int [] [.fail] := by
  refine .let_ (live := true) rfl (.new .lit) ?_
  have := Typed.handle (F := []) (O := ops) (Γ := [("base", .own (.box .int) true)]) (e := 0) (op := ops[0])
    (os := []) (rs := []) (caps := [("b", deref (var "base"))]) (ts := [.int]) (ys := ["base"]) (r := [.fail])
    (arm := .add (.read (var "b")) (.lit 1)) (Γa := [("b", .ref .ro .int)])
    (body := .add (.perform 0 [] []) (.read (deref (var "base")))) (τ := .int)
    (Γb := [("base", .ref .ro (.box .int))])
    rfl rfl rfl (.cons (.deref (.own rfl)) .nil) (by decide)
    (.add (.read (.ref rfl)) .lit)
    (.add (.perform (op := { owns := [], refs := [], ret := .int }) rfl (List.mem_cons_self ..) .nil .nil
      List.Pairwise.nil) (.read (.deref (.ref rfl))))
  simpa [thaw] using this

example : ∀ n, match eval [] ops n [.abort .fail 0] .empty [] asks with
    | (.stuck, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (fun _ h => by simp at h) asks_typed

/-- `let x = Box.new(1); handle { let y = Box.new(2); Stop.stop(*y) } with Stop { stop(e) => e + *x }`:
the operation unwinds out of `y`'s scope, which drops it, to the arm, which sees `x`; 3, and nothing
left allocated. -/
def stops : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1))
    (.handleAbort (.let_ "y" (.box .int) (.new (.lit 2)) (.perform 1 [.read (deref (var "y"))] [])) 1 "e"
      (.add (.read (var "e")) (.read (deref (var "x")))))

example : (eval [] ops 20 [] .empty [] stops).1 = .val (.int 3) := by decide
example : ∀ l < (eval [] ops 20 [] .empty [] stops).2.next, (eval [] ops 20 [] .empty [] stops).2.mem l = none := by
  decide

theorem stops_typed : Typed [] ops [] stops .int [] [.fail] :=
  .let_ rfl (.new .lit) (.handleAbort rfl rfl rfl rfl
    (.let_ rfl (.new .lit) (.perform (op := { owns := [.int], refs := [], ret := .int }) rfl (List.mem_cons_self ..)
      (.cons (.read (.deref (.own rfl))) .nil) .nil List.Pairwise.nil))
    (.add (.read (.own rfl)) (.read (.deref (.own rfl)))))

/-- `let x = Box.new(1); handle { x = Box.new(2); Ask.ask() } with Ask { ask() resumes k => k(*b) }`,
the arm lent `*x` as `b`: the body would free the cell the arm reads. The types reject it: what a
`handle` lends its arm, its body may only read. -/
def clobbers : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1))
    (.handle (.seq (.assign (var "x") (.box .int) (.new (.lit 2))) (.perform 0 [] [])) 0 [("b", deref (var "x"))] [] []
      (.read (var "b")))

/-- What a `handle` lends its arm, and its body, typed where those places are only read. -/
theorem handle_inv : Typed F O Γ (.handle body e caps os rs arm) τ Γ' r →
    ∃ ts ys Γb, Caps Γ caps ts ys ∧ Typed F O (freeze Γ ys) body τ Γb (.eff e :: r) := by
  intro h
  cases h with
  | handle _ _ _ hc _ _ hb => exact ⟨_, _, _, hc, hb⟩

theorem clobbers_rejected : ¬ Typed [] ops [] clobbers τ Γ' r := by
  intro h
  cases h with
  | let_ _ _ hb =>
    obtain ⟨ts, ys, Γb, hc, hbody⟩ := handle_inv hb
    cases hc with
    | cons hp hc =>
      cases hc
      have hroot : ∀ {Γ τ w y}, PlaceTy Γ (deref (var "x")) τ w y → y = "x" := by
        intro Γ τ w y hp; cases hp with | deref hq => cases hq <;> rfl
      obtain rfl := hroot hp
      cases hbody with
      | seq ha _ =>
        cases ha with
        | assign hv hp' =>
          cases hv with
          | new hl =>
            cases hl
            have hx : ∀ {Γ τ w y}, PlaceTy Γ (var "x") τ w y → y = "x" := by
              intro Γ τ w y hp; cases hp <;> rfl
            have := hx hp'
            subst this
            exact Bool.noConfusion (hp'.frozen (List.mem_singleton_self _))

/-- `let x = Box.new(1); try { defer { *x = 5 }; let y = Box.new(2); throw *y } catch (e) { e + *x }`:
the cleanup runs as the failure leaves its block, before the handler, which sees what it wrote; 7,
and nothing left allocated. -/
def cleans : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1))
    (.try_ (.defer .int (.write (deref (var "x")) (.lit 5))
        (.let_ "y" (.box .int) (.new (.lit 2)) (.throw_ (.read (deref (var "y")))))) "e"
      (.add (.read (var "e")) (.read (deref (var "x")))))

example : (eval [] [] 20 [] .empty [] cleans).1 = .val (.int 7) := by decide
example : ∀ l < (eval [] [] 20 [] .empty [] cleans).2.next, (eval [] [] 20 [] .empty [] cleans).2.mem l = none := by
  decide

theorem cleans_typed : Typed [] [] [] cleans .int [] [.fail] :=
  .let_ rfl (.new .lit) (.try_ rfl
    (.defer (.let_ rfl (.new .lit) (.throw_ (.read (.deref (.own rfl))) (List.mem_cons_self ..)))
      (.write .lit (.deref (.own rfl))))
    (.add (.read (.own rfl)) (.read (.deref (.own rfl)))))

end FlyCore.Ownership.Examples
