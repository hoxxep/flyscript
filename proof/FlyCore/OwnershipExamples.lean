import FlyCore.OwnershipSound

/-!
The semantics computes what the language means: a program that lends and moves ends with every cell
freed, handlers resume and unwind dropping what the scopes they leave own, an arm that fails drops
the code its `handle` ran, cleanups and all, and the aliasing the types forbid is a use after free.
-/

namespace FlyCore.Ownership.Examples

open Expr Place

set_option linter.unusedSimpArgs false

/-- The integer a run gave. -/
def value : Res × Store → Option Int
  | (.val (.int k), _) => some k
  | _ => none

/-- Whether no cell below `n` is allocated. -/
def freedBelow (σ : Store) : Nat → Bool
  | 0 => true
  | n + 1 => (σ.mem n).isNone && freedBelow σ n

/-- Whether a run left nothing allocated. -/
def freed (r : Res × Store) : Bool := freedBelow r.2 r.2.next

def isStuck : Res × Store → Bool
  | (.stuck, _) => true
  | _ => false

/-- Runs a program: the evaluator unfolded by its equations. -/
syntax "run" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| run [$xs,*]) => `(tactic| simp [eval, ret, evalK, evalAtom, evalAtoms, resolve, leave, cleanV,
      cleanA, dropRet, armEnd, allocAll, dropCells, dropCell, drop, dropK, pick, Store.fresh, Store.alloc, Store.set, find,
      Frame.handles, Kont.push, lookup, Res.done, Outcome.res, Cap.at, Store.empty, value, freed, freedBelow,
      isStuck, $xs,*])

/-- `function add(b: Box<int>, r: mut Box<int>): int { *r = *r + *b; *r }` -/
def addInto : Fn :=
  { owns := [("b", .box .int)], refs := [("r", .mut, .box .int)], ret := .int, row := [],
    body := .let_ "t" .int (.add (.read (deref (var "r"))) (.read (deref (var "b"))))
      (.let_ "u" .int (.write (deref (var "r")) (.read (var "t"))) (.atom (.read (deref (var "r"))))) }

/-- `let x = Box.new(1); let y = Box.new(41); addInto(y, mut x)`: 42, and nothing left allocated. -/
def lends : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1))
    (.let_ "y" (.box .int) (.new (.lit 41))
      (.call 0 [.move "y"] [(.mut, var "x")]))

example : value (eval [addInto] [] 20 [] .empty [] lends) = some 42 := by
  run [lends, addInto]
example : freed (eval [addInto] [] 20 [] .empty [] lends) := by
  run [lends, addInto]

/-- `function g(a: mut Box<int>, c: int (readonly)): int { a = Box.new(7); c }`, called with
`mut x` and `readonly *x`: the assignment frees the cell `c` borrows. -/
def clobber : Fn :=
  { owns := [], refs := [("a", .mut, .box .int), ("c", .ro, .int)], ret := .int, row := [],
    body := .let_ "t" (.box .int) (.new (.lit 7))
      (.let_ "u" .int (.assign (var "a") (.box .int) (.move "t")) (.atom (.read (var "c")))) }

def aliased : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1)) (.call 0 [] [(.mut, var "x"), (.ro, deref (var "x"))])

example : isStuck (eval [clobber] [] 20 [] .empty [] aliased) := by
  run [aliased, clobber]

/-! The types accept `lends`, so `program_ok` covers it; they reject `aliased`. -/

theorem addInto_ok : FnsOk [addInto] [] := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  refine ⟨by decide, _, .let_ rfl (.add (.read (.deref (.ref (m := .mut) rfl))) (.read (.deref (.own rfl))))
    (.let_ rfl (.write (.read (.own rfl)) (.deref (.ref (m := .mut) rfl)))
      (.atom (.read (.deref (.ref (m := .mut) rfl)))))⟩

theorem lends_typed : Typed [addInto] [] [] lends .int [] [.fail] := by
  have hc : Typed [addInto] [] [("y", .own (.box .int) true), ("x", .own (.box .int) true)]
      (.call 0 [.move "y"] [(.mut, var "x")]) .int
      [("y", .own (.box .int) false), ("x", .own (.box .int) true)] [.fail] := by
    have := Typed.call (F := [addInto]) (O := []) (Γ := [("y", .own (.box .int) true), ("x", .own (.box .int) true)])
      (f := 0) (d := addInto) (ys := [(.mut, "x")]) (r := [.fail]) rfl rfl rfl (by simp [addInto])
      (.cons (.move (x := "y") rfl rfl) .nil) (.cons (.own (by simp [lookup, setSlot])) (fun _ => rfl) rfl .nil)
      (by simp [LentApart])
    simpa [setSlot, addInto] using this
  exact .let_ rfl (.new .lit) (.let_ rfl (.new .lit) hc)

example : ∀ n, match eval [addInto] [] n [.abort .fail 0] .empty [] lends with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT [addInto] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok addInto_ok lends_typed

/-- `let x = Box.new(1); try { let y = Box.new(2); throw *y } catch (e) { e + *x }`: the failure
leaves `y`'s scope, which drops it, and the handler sees `x`; 3, and nothing left allocated. -/
def unwinds : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1))
    (.try_ (.let_ "y" (.box .int) (.new (.lit 2)) (.throw_ (.read (deref (var "y"))))) "e"
      (.add (.read (var "e")) (.read (deref (var "x")))))

example : value (eval [] [] 20 [] .empty [] unwinds) = some 3 := by
  run [unwinds]
example : freed (eval [] [] 20 [] .empty [] unwinds) := by
  run [unwinds]

theorem unwinds_typed : Typed [] [] [] unwinds .int [] [] :=
  .let_ rfl (.new .lit) (.try_ rfl (.let_ rfl (.new .lit) (.throw_ (.read (.deref (.own rfl))) (by simp)))
    (.add (.read (.own rfl)) (.read (.deref (.own rfl)))))

theorem aliased_rejected : ¬ Typed [clobber] O [] aliased τ Γ' r := by
  intro h
  cases h with
  | let_ _ _ hb =>
    cases hb with
    | call hf _ _ _ _ hl hx =>
      simp at hf
      subst hf
      cases hl with
      | cons hp _ _ hl =>
        cases hl with
        | cons hp' _ _ hl =>
          cases hl
          cases hp
          · cases hp' with
            | deref hq => cases hq <;> simp_all [LentApart, Place.root, Place.Apart.not_var]
          · simp_all [lookup]
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
    (.handle .int (.let_ "a" .int (.perform 0 [] []) (.add (.read (var "a")) (.read (deref (var "base"))))) 0
      [⟨"b", .ro, .int, deref (var "base")⟩] [] []
      (.add (.read (var "b")) (.lit 1)))

example : value (eval [] ops 20 [] .empty [] asks) = some 81 := by
  run [asks, ops]
example : freed (eval [] ops 20 [] .empty [] asks) := by
  run [asks, ops]

theorem asks_typed : Typed [] ops [] asks .int [] [.fail] := by
  refine .let_ (live := true) rfl (.new .lit) ?_
  have := Typed.handle (F := []) (O := ops) (Γ := [("base", .own (.box .int) true)]) (e := 0) (op := ops[0])
    (os := []) (rs := []) (caps := [⟨"b", .ro, .int, deref (var "base")⟩]) (ys := [(.ro, "base")]) (r := [.fail])
    (arm := .add (.read (var "b")) (.lit 1)) (Γa := [("b", .ref .ro .int)])
    (body := .let_ "a" .int (.perform 0 [] []) (.add (.read (var "a")) (.read (deref (var "base"))))) (τ := .int)
    (Γb := [("base", .ref .ro (.box .int))])
    rfl (by simp [ops]) rfl rfl (.ro (.deref (.own rfl)) rfl .nil) (by simp [Exclusive]) (by decide)
    (.add (.read (.ref rfl)) .lit)
    (.let_ rfl (.perform (op := { owns := [], refs := [], ret := .int }) rfl (List.mem_cons_self ..) .nil .nil
      List.Pairwise.nil) (.add (.read (.own rfl)) (.read (.deref (.ref rfl)))))
  simpa [thaw, unhideAll, hideAll, roots] using this

example : ∀ n, match eval [] ops n [.abort .fail 0] .empty [] asks with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (fun _ h => by simp at h) asks_typed

/-- `let x = Box.new(1); handle { let y = Box.new(2); Stop.stop(*y) } with Stop { stop(e) => e + *x }`:
the operation unwinds out of `y`'s scope, which drops it, to the arm, which sees `x`; 3, and nothing
left allocated. -/
def stops : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1))
    (.handleAbort (.let_ "y" (.box .int) (.new (.lit 2)) (.perform 1 [.read (deref (var "y"))] [])) 1 "e"
      (.add (.read (var "e")) (.read (deref (var "x")))))

example : value (eval [] ops 20 [] .empty [] stops) = some 3 := by
  run [stops, ops]
example : freed (eval [] ops 20 [] .empty [] stops) := by
  run [stops, ops]

theorem stops_typed : Typed [] ops [] stops .int [] [.fail] :=
  .let_ rfl (.new .lit) (.handleAbort rfl rfl rfl rfl
    (.let_ rfl (.new .lit) (.perform (op := { owns := [.int], refs := [], ret := .int }) rfl (List.mem_cons_self ..)
      (.cons (.read (.deref (.own rfl))) .nil) .nil List.Pairwise.nil))
    (.add (.read (.own rfl)) (.read (.deref (.own rfl)))))

/-- `let x = Box.new(1); try { handle { defer { *x = 5 }; let y = Box.new(2); Ask.ask() + *y } with
Ask { ask() resumes k => throw 7 } } catch (e) { e + *x }`: the arm fails, so the code its `handle`
ran is dropped — `y` freed, the cleanup run — and the failure goes on to the handler, which sees what
the cleanup wrote; 12, and nothing left allocated. -/
def drops : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1))
    (.try_
      (.handle .int
        (.defer .int (.write (deref (var "x")) (.lit 5))
          (.let_ "y" (.box .int) (.new (.lit 2))
            (.let_ "a" .int (.perform 0 [] []) (.add (.read (var "a")) (.read (deref (var "y")))))))
        0 [] [] [] (.throw_ (.lit 7)))
      "e" (.add (.read (var "e")) (.read (deref (var "x")))))

example : value (eval [] ops 20 [] .empty [] drops) = some 12 := by
  run [drops, ops]
example : freed (eval [] ops 20 [] .empty [] drops) := by
  run [drops, ops]

theorem drops_typed : Typed [] ops [] drops .int [] [.fail] := by
  have hb := Typed.handle (F := []) (O := ops) (Γ := [("x", .own (.box .int) true)]) (e := 0) (op := ops[0])
    (os := []) (rs := []) (caps := []) (ys := []) (r := [.fail, .fail]) (arm := .throw_ (.lit 7)) (Γa := [])
    (body := .defer .int (.write (deref (var "x")) (.lit 5))
      (.let_ "y" (.box .int) (.new (.lit 2))
        (.let_ "a" .int (.perform 0 [] []) (.add (.read (var "a")) (.read (deref (var "y")))))))
    (τ := .int) (Γb := [("x", .own (.box .int) true)])
    rfl (by simp [ops]) rfl rfl .nil (by simp [Exclusive]) (by decide) (.throw_ .lit (List.mem_cons_self ..))
    (.defer (.let_ (live := true) rfl (.new .lit)
        (.let_ (live := true) rfl (.perform (op := { owns := [], refs := [], ret := .int }) rfl
          (List.mem_cons_self ..) .nil .nil List.Pairwise.nil) (.add (.read (.own rfl)) (.read (.deref (.own rfl))))))
      (.write .lit (.deref (.own rfl))))
  simp [thaw, unhideAll, hideAll, freeze, roots] at hb
  exact .let_ (live := true) rfl (.new .lit) (.try_ rfl hb (.add (.read (.own rfl)) (.read (.deref (.own rfl)))))

example : ∀ n, match eval [] ops n [.abort .fail 0] .empty [] drops with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (fun _ h => by simp at h) drops_typed

/-- `let x = Box.new(1); handle { x = Box.new(2); Ask.ask() } with Ask { ask() resumes k => k(*b) }`,
the arm lent `*x` as `b`: the body would free the cell the arm reads. The types reject it: what a
`handle` lends its arm, its body may only read. -/
def clobbers : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1))
    (.handle .int (.let_ "t" (.box .int) (.new (.lit 2))
        (.let_ "u" .int (.assign (var "x") (.box .int) (.move "t")) (.perform 0 [] []))) 0
      [⟨"b", .ro, .int, deref (var "x")⟩] [] [] (.atom (.read (var "b"))))

/-- A variable that may be changed through is owned and live, or a `mut` borrow. -/
theorem var_writable (h : PlaceTy Γ (var x) τ w y) (hw : w = true) :
    lookup x Γ = some (.own τ true) ∨ lookup x Γ = some (.ref .mut τ) ∨ ∃ t A B, lookup x Γ = some (.half t A B) := by
  cases h with
  | own hx => exact .inl hx
  | ref hx =>
    rename_i m
    cases m with
    | ro => simp at hw
    | «mut» => exact .inr (.inl hx)
  | half hx _ => exact .inr (.inr ⟨_, _, _, hx⟩)

/-- What a `handle` lends its arm, and its body, typed where those places lent `readonly` are only
read and those lent `mut` out of reach. -/
theorem handle_inv : Typed F O Γ (.handle τ body e caps os rs arm) τ' Γ' r →
    ∃ ys Γb, Caps Γ caps ys ∧ Typed F O (freeze (hideAll Γ (roots .mut ys)) (roots .ro ys)) body τ Γb (.eff e :: r) := by
  intro h
  cases h with
  | handle _ _ _ _ hc _ _ _ hb => exact ⟨_, _, hc, hb⟩

theorem clobbers_rejected : ¬ Typed [] ops [] clobbers τ Γ' r := by
  intro h
  cases h with
  | let_ _ h0 hb =>
    cases h0 with
    | new h0 =>
    cases h0
    obtain ⟨ys, Γb, hc, hbody⟩ := handle_inv hb
    cases hc with
    | ro hp _ hc =>
      cases hc
      simp only [roots, List.filter] at hbody
      have hroot : ∀ {Γ τ w y}, PlaceTy Γ (deref (var "x")) τ w y → y = "x" := by
        intro Γ τ w y hp; cases hp with | deref hq => cases hq <;> rfl
      obtain rfl := hroot hp
      cases hbody with
      | let_ _ hn hb =>
        cases hn with
        | new hl =>
          cases hl
          cases hb with
          | let_ _ ha _ =>
            cases ha with
            | assign hv hp' =>
              cases hv
              rename_i hc
              rcases var_writable hp' rfl with h | h | ⟨_, _, _, h⟩ <;>
                simp [lookup, freeze, hideAll, setSlot, Slot.ro] at h

/-- `let n = 0; (handle { Ask.ask() + Ask.ask() } with Ask { ask() resumes k => { c = c + 1; k(c) } }) + n`,
the arm lent `n` as `c`, `mut`: state an arm keeps from one operation to the next, which the body
cannot reach while the `handle` runs. The operations give 1 and 2, and `n` is 2 after; 5. -/
def counts : Expr :=
  .let_ "n" .int (.atom (.lit 0))
    (.let_ "h" .int
      (.handle .int (.let_ "a" .int (.perform 0 [] []) (.let_ "b" .int (.perform 0 [] []) (.add (.read (var "a")) (.read (var "b")))))
        0 [⟨"c", .mut, .int, var "n"⟩] [] []
        (.let_ "t" .int (.add (.read (var "c")) (.lit 1)) (.let_ "u" .int (.write (var "c") (.read (var "t")))
          (.atom (.read (var "c"))))))
      (.add (.read (var "h")) (.read (var "n"))))

example : value (eval [] ops 20 [] .empty [] counts) = some 5 := by
  run [counts, ops]
example : freed (eval [] ops 20 [] .empty [] counts) := by
  run [counts, ops]

theorem counts_typed : Typed [] ops [] counts .int [] [.fail] := by
  have := Typed.handle (F := []) (O := ops) (Γ := [("n", .own .int true)]) (e := 0) (op := ops[0])
    (os := []) (rs := []) (caps := [⟨"c", .mut, .int, var "n"⟩]) (ys := [(.mut, "n")]) (r := [.fail])
    (arm := .let_ "t" .int (.add (.read (var "c")) (.lit 1)) (.let_ "u" .int (.write (var "c") (.read (var "t")))
      (.atom (.read (var "c")))))
    (Γa := [("c", .ref .mut .int)])
    (body := .let_ "a" .int (.perform 0 [] []) (.let_ "b" .int (.perform 0 [] []) (.add (.read (var "a")) (.read (var "b")))))
    (τ := .int) (Γb := [("n", .lent .int)])
    rfl (by simp [ops]) rfl rfl (.mut (.own rfl) rfl rfl .nil) (by simp [Exclusive]) (by decide)
    (.let_ (live := true) rfl (.add (.read (.ref rfl)) .lit)
      (.let_ (live := true) rfl (.write (.read (.own rfl)) (.ref (m := .mut) rfl)) (.atom (.read (.ref rfl)))))
    (.let_ (live := true) rfl (.perform (op := { owns := [], refs := [], ret := .int }) rfl (List.mem_cons_self ..)
        .nil .nil List.Pairwise.nil)
      (.let_ (live := true) rfl (.perform (op := { owns := [], refs := [], ret := .int }) rfl (List.mem_cons_self ..)
          .nil .nil List.Pairwise.nil)
        (.add (.read (.own rfl)) (.read (.own rfl)))))
  simp [thaw, unhideAll, hideAll, hide, roots, Slot.ty] at this
  exact .let_ (live := true) rfl (.atom .lit) (.let_ (live := true) rfl this
    (.add (.read (.own rfl)) (.read (.own rfl))))

example : ∀ n, match eval [] ops n [.abort .fail 0] .empty [] counts with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (fun _ h => by simp at h) counts_typed

/-- `let n = 0; handle { n = 5; Ask.ask() } with Ask { ask() resumes k => { c = c + 1; k(c) } }`: the
body changes the state its arm was lent `mut`. The types reject it: what an arm keeps, the body
cannot reach. -/
def meddles : Expr :=
  .let_ "n" .int (.atom (.lit 0))
    (.handle .int (.let_ "u" .int (.write (var "n") (.lit 5)) (.perform 0 [] [])) 0 [⟨"c", .mut, .int, var "n"⟩] [] []
      (.let_ "t" .int (.add (.read (var "c")) (.lit 1)) (.let_ "u" .int (.write (var "c") (.read (var "t")))
        (.atom (.read (var "c"))))))

/-- A variable out of reach is no place. -/
theorem lent_unreachable (h : lookup x Γ = some (.lent τ')) : ¬ PlaceTy Γ (var x) τ w y := by
  intro hp; cases hp <;> simp_all

theorem meddles_rejected : ¬ Typed [] ops [] meddles τ Γ' r := by
  intro h
  cases h with
  | let_ _ ha hb =>
    cases ha with
    | atom ha =>
    cases ha
    obtain ⟨ys, Γb, hc, hbody⟩ := handle_inv hb
    cases hc with
    | «mut» hp _ _ hc =>
      cases hc
      cases hbody with
      | let_ _ ha _ =>
        cases ha with
        | write ha hq =>
          cases ha
          exact lent_unreachable (τ' := .int) (by decide) hq

/-- `let x = Box.new(1); try { defer { *x = 5 }; let y = Box.new(2); throw *y } catch (e) { e + *x }`:
the cleanup runs as the failure leaves its block, before the handler, which sees what it wrote; 7,
and nothing left allocated. -/
def cleans : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1))
    (.try_ (.defer .int (.write (deref (var "x")) (.lit 5))
        (.let_ "y" (.box .int) (.new (.lit 2)) (.throw_ (.read (deref (var "y")))))) "e"
      (.add (.read (var "e")) (.read (deref (var "x")))))

example : value (eval [] [] 20 [] .empty [] cleans) = some 7 := by
  run [cleans]
example : freed (eval [] [] 20 [] .empty [] cleans) := by
  run [cleans]

theorem cleans_typed : Typed [] [] [] cleans .int [] [.fail] :=
  .let_ rfl (.new .lit) (.try_ rfl
    (.defer (.let_ rfl (.new .lit) (.throw_ (.read (.deref (.own rfl))) (List.mem_cons_self ..)))
      (.write .lit (.deref (.own rfl))))
    (.add (.read (.own rfl)) (.read (.deref (.own rfl)))))

/-- `let x = Box.new(1); { const r = mut *x; r = r + 41 }; *x`: the borrow changes what `x` owns,
and once it ends `x` reads what it left; 42, and nothing left allocated. -/
def borrows : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1))
    (.let_ "u" .int (.lend "r" .mut (deref (var "x"))
        (.let_ "t" .int (.add (.read (var "r")) (.lit 41)) (.write (var "r") (.read (var "t")))))
      (.atom (.read (deref (var "x")))))

example : value (eval [] [] 20 [] .empty [] borrows) = some 42 := by
  run [borrows]
example : freed (eval [] [] 20 [] .empty [] borrows) := by
  run [borrows]

theorem borrows_typed : Typed [] [] [] borrows .int [] [.fail] := by
  have := Typed.lend (F := []) (O := []) (Γ := [("x", .own (.box .int) true)]) (x := "r") (m := .mut)
    (p := deref (var "x")) (τ := .int) (w := true) (y := "x") (r := [.fail])
    (body := .let_ "t" .int (.add (.read (var "r")) (.lit 41)) (.write (var "r") (.read (var "t")))) (τb := .int)
    (Γb := [("x", .lent (.box .int))]) rfl (.deref (.own rfl)) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ _ _ h => by simp [lookup] at h)
    (.let_ (live := true) rfl (.add (.read (.ref rfl)) .lit) (.write (.read (.own rfl)) (.ref (m := .mut) rfl)))
  simp only [thaw] at this
  exact .let_ (live := true) rfl (.new .lit) (.let_ (live := true) rfl (by simpa using this)
    (.atom (.read (.deref (.own rfl)))))

/-- `let x = Box.new(20); { const r = readonly x; *r + *x }`: a `readonly` borrow and what it
borrows, both read; 40. -/
def reads : Expr :=
  .let_ "x" (.box .int) (.new (.lit 20))
    (.lend "r" .ro (var "x") (.add (.read (deref (var "r"))) (.read (deref (var "x")))))

example : value (eval [] [] 20 [] .empty [] reads) = some 40 := by
  run [reads]

/-- `let x = Box.new(1); { const r = mut *x; *x }`: `x` reached while lent `mut`. The types reject
it: nothing may reach what a `mut` borrow has while it lives. -/
def reaches : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1)) (.lend "r" .mut (deref (var "x")) (.atom (.read (deref (var "x")))))

/-- What a borrow is of, and the code it is in scope for, typed with its root out of reach. -/
theorem lend_inv (hnf : ∀ t y, p ≠ fieldOf t y) : Typed F O Γ (.lend x m p body) τ Γ' r →
    ∃ τp w y Γb, PlaceTy Γ p τp w y ∧ Typed F O ((x, .ref m τp) :: lendCtx m Γ y) body τ ((x, .ref m τp) :: Γb) r := by
  intro h
  cases h with
  | lend _ hp _ _ _ hb => exact ⟨_, _, _, _, hp, hb⟩
  | lendField => exact absurd rfl (hnf _ _)

theorem reaches_rejected : ¬ Typed [] O [] reaches τ Γ' r := by
  intro h
  cases h with
  | let_ _ _ hb =>
    obtain ⟨τp, w, y, Γb, hp, hbody⟩ := lend_inv (fun t y h => by cases t <;> simp [fieldOf] at h) hb
    have hy : y = "x" := by cases hp with | deref hq => cases hq <;> rfl
    subst hy
    · cases hbody with
      | atom ha =>
        cases ha with
        | read hq =>
          cases hq with
          | deref hq =>
            cases hq with
            | own hx => simp [lendCtx, hide, lookup] at hx
            | ref hx => simp [lendCtx, hide, lookup] at hx
            | half hx => simp [lendCtx, hide, lookup] at hx

/-! A borrow a function returns. -/

/-- `function inside(r: mut Box<int>): mut int { r.* }`: a borrow of what the box it was lent holds. -/
def inside : Fn :=
  { owns := [], refs := [("r", .mut, .box .int)], ret := .int, row := [], body := .atom (.lit 0),
    retp := some (.mut, [(0, deref (var "r"))]) }

/-- `let x = Box.new(1); { const v = inside(mut x); v = v + 41 }; *x`: the borrow the call returns
changes what `x` holds, and once it ends `x` reads what it left; 42, and nothing left allocated. -/
def returns : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1))
    (.let_ "u" .int (.lendCall "v" .mut 0 [] [(.mut, var "x")]
        (.let_ "t" .int (.add (.read (var "v")) (.lit 41)) (.write (var "v") (.read (var "t")))))
      (.atom (.read (deref (var "x")))))

example : value (eval [inside] [] 20 [] .empty [] returns) = some 42 := by
  run [returns, inside]
example : freed (eval [inside] [] 20 [] .empty [] returns) := by
  run [returns, inside]

theorem inside_ok : FnsOk [inside] [] := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  refine ⟨by decide, by simp, _, .atom .lit, fun c hc => ?_⟩
  simp only [List.mem_singleton] at hc
  subst hc
  exact ⟨"r", .mut, .box .int, true, rfl, .deref (.ref (m := .mut) rfl), fun _ => rfl⟩

theorem returns_typed : Typed [inside] [] [] returns .int [] [.fail] := by
  have := Typed.lendCall (F := [inside]) (O := []) (Γ := [("x", .own (.box .int) true)]) (f := 0) (d := inside)
    (m := .mut) (cs := [(0, deref (var "r"))]) (r := [.fail]) (owned := []) (Γ₁ := [("x", .own (.box .int) true)])
    (lent := [(.mut, var "x")]) (ys := [(.mut, "x")]) (zs := ["x"]) (x := "v")
    (body := .let_ "t" .int (.add (.read (var "v")) (.lit 41)) (.write (var "v") (.read (var "t"))))
    (τb := .int) (Γb := [("x", .lent (.box .int))])
    rfl rfl rfl (by simp [inside]) .nil (.cons (.own rfl) (fun _ => rfl) rfl .nil) (by simp [LentApart])
    (.cons ⟨.mut, rfl, fun _ => rfl⟩ .nil)
    (fun _ => ⟨by simp, rfl, by simp [inside, Ty.isFn], fun z hz t A B h => by simp at hz; subst hz; simp [lookup] at h⟩) rfl
    (.let_ (live := true) rfl (.add (.read (.ref rfl)) .lit) (.write (.read (.own rfl)) (.ref (m := .mut) rfl)))
  simp only [unlend, unhideAll, thaw] at this
  exact .let_ (live := true) rfl (.new .lit) (.let_ (live := true) rfl (by simpa using this)
    (.atom (.read (.deref (.own rfl)))))

example : ∀ n, match eval [inside] [] n [.abort .fail 0] .empty [] returns with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT [inside] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok inside_ok returns_typed

/-- `let x = Box.new(1); { const v = inside(mut x); *x }`: `x` reached while the borrow the call
returned lives. The types reject it, as for a borrow of a place. -/
def reachesReturned : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1))
    (.lendCall "v" .mut 0 [] [(.mut, var "x")] (.atom (.read (deref (var "x")))))

/-- What a call that returns a borrow lends, and the code the borrow is in scope for. -/
theorem lendCall_inv : Typed F O Γ (.lendCall x m f owned lent body) τ Γ' r →
    ∃ d cs Γ₁ ys zs Γb, F[f]? = some d ∧ d.retp = some (m, cs) ∧
      AtomsTy Γ owned (d.owns.map Prod.snd) Γ₁ ∧ Lends Γ₁ lent (d.refs.map Prod.snd) ys ∧
      Pairs (fun c z => ∃ mi, ys[c.1]? = some (mi, z) ∧ (m = .mut → mi = .mut)) cs zs ∧
      Typed F O ((x, .ref m d.ret) :: lendCtxs m Γ₁ zs) body τ ((x, .ref m d.ret) :: Γb) r := by
  intro h
  cases h with
  | lendCall hf hret _ _ ha hl _ hp _ _ hb => exact ⟨_, _, _, _, _, _, hf, hret, ha, hl, hp, hb⟩

theorem reachesReturned_rejected : ¬ Typed [inside] [] [] reachesReturned τ Γ' r := by
  intro h
  cases h with
  | let_ _ _ hb =>
    obtain ⟨d, cs, Γ₁, ys, zs, Γb, hf, hret, ha, hl, hpairs, hbody⟩ := lendCall_inv hb
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      simp only [inside, Option.some.injEq, Prod.mk.injEq] at hret
      obtain ⟨-, rfl⟩ := hret
      cases ha
      cases hl with
      | cons hp _ hl =>
        cases hl
        cases hpairs with
        | cons hyi hrest =>
        cases hrest
        obtain ⟨mi, hyi, -⟩ := hyi
        simp at hyi
        obtain ⟨-, rfl⟩ := hyi
        cases hp with
        | ref hx => simp [lookup] at hx
        | half hx => simp [lookup] at hx
        | own _ =>
        cases hbody with
        | atom ha =>
          cases ha with
          | read hq =>
            cases hq with
            | deref hq =>
              cases hq with
              | own hx => simp [lendCtx, lendCtxs, hideAll, hide, lookup] at hx
              | ref hx => simp [lendCtx, lendCtxs, hideAll, hide, lookup] at hx
              | half hx => simp [lendCtx, lendCtxs, hideAll, hide, lookup] at hx

/-! Closures that own what they captured. -/

/-- `(x) => { *c = *c + x; *c }`, capturing a box `c`, called through a `mut` borrow: a counter. -/
def bump : Fn :=
  { owns := [("x", .int)], refs := [], ret := .int, row := [],
    body := .let_ "t" .int (.add (.read (deref (var "c"))) (.read (var "x")))
      (.let_ "u" .int (.write (deref (var "c")) (.read (var "t"))) (.atom (.read (deref (var "c"))))),
    cap := some ("c", .box .int, .excl) }

/-- `let b = Box.new(40); let f = (x) => { … }; f(1); f(1)`: the closure keeps its box from one call
to the next; 42, and once `f` goes out of scope, its box with it: nothing left allocated. -/
def counter : Expr :=
  .let_ "b" (.box .int) (.new (.lit 40))
    (.let_ "f" (.fn .excl .int .int []) (.lam 0 (.move "b"))
      (.let_ "u" .int (.apply .excl (var "f") (.lit 1)) (.apply .excl (var "f") (.lit 1))))

example : value (eval [bump] [] 30 [] .empty [] counter) = some 42 := by
  run [counter, bump, cloFn]
example : freed (eval [bump] [] 30 [] .empty [] counter) := by
  run [counter, bump, cloFn]

theorem bump_ok : FnsOk [bump] [] := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  refine ⟨by decide, by decide, _, .let_ (live := true) rfl (.add (.read (.deref (.ref (m := .mut) rfl))) (.read (.own rfl)))
    (.let_ (live := true) rfl (.write (.read (.own rfl)) (.deref (.ref (m := .mut) rfl)))
      (.atom (.read (.deref (.ref (m := .mut) rfl)))))⟩

theorem counter_typed : Typed [bump] [] [] counter .int [] [.fail] := by
  have hlam : Typed [bump] [] [("b", .own (.box .int) true)] (.lam 0 (.move "b")) (.fn .excl .int .int [])
      [("b", .own (.box .int) false)] [.fail] := by
    have := Typed.lam (F := [bump]) (O := []) (Γ := [("b", .own (.box .int) true)]) (f := 0) (d := bump)
      (r := [.fail]) rfl rfl rfl rfl rfl (.move (x := "b") rfl rfl)
    simpa [bump, setSlot] using this
  exact .let_ (live := false) rfl (.new .lit)
    (.let_ (live := true) rfl hlam
      (.let_ (live := true) rfl (.applyBorrow (by decide) .lit (.own rfl) (fun _ => rfl) (by simp))
        (.applyBorrow (by decide) .lit (.own rfl) (fun _ => rfl) (by simp))))

example : ∀ n, match eval [bump] [] n [.abort .fail 0] .empty [] counter with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT [bump] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok bump_ok counter_typed

/-- `(x) => *c + x`, capturing a box `c`, called once: the call consumes it, its box dropped as the
body ends. -/
def spend : Fn :=
  { owns := [("x", .int)], refs := [], ret := .int, row := [],
    body := .add (.read (deref (var "c"))) (.read (var "x")), cap := some ("c", .box .int, .once) }

/-- `let b = Box.new(40); let f = (x) => *c + x; f(2)`: 42, and nothing left allocated. -/
def spends : Expr :=
  .let_ "b" (.box .int) (.new (.lit 40))
    (.let_ "f" (.fn .once .int .int []) (.lam 0 (.move "b")) (.apply .once (var "f") (.lit 2)))

example : value (eval [spend] [] 30 [] .empty [] spends) = some 42 := by
  run [spends, spend, cloFn]
example : freed (eval [spend] [] 30 [] .empty [] spends) := by
  run [spends, spend, cloFn]

/-- `f(2); f(2)` for a closure called once: the types reject the second call. -/
def spendsTwice : Expr :=
  .let_ "b" (.box .int) (.new (.lit 40))
    (.let_ "f" (.fn .once .int .int []) (.lam 0 (.move "b"))
      (.let_ "u" .int (.apply .once (var "f") (.lit 2)) (.apply .once (var "f") (.lit 2))))

theorem spendsTwice_rejected : ¬ Typed [spend] [] [] spendsTwice τ Γ' r := by
  intro h
  cases h with
  | let_ _ _ hb =>
    cases hb with
    | let_ _ _ hb =>
      cases hb with
      | let_ _ h1 h2 =>
        cases h1 with
        | applyBorrow hk => exact absurd rfl hk
        | applyOnce hx _ ha =>
          cases ha
          cases h2 with
          | applyBorrow hk => exact absurd rfl hk
          | applyOnce hx' => simp [setSlot, lookup] at hx'

/-! A closure over a borrow, and a function that takes one. -/

/-- `(x) => x + *c`, over a `readonly` borrow `c` of a box. -/
def addTo : Fn :=
  { owns := [("x", .int)], refs := [], ret := .int, row := [],
    body := .add (.read (var "x")) (.read (deref (var "c"))), cap := some ("c", .box .int, .shared) }

/-- `function twice(x: int, g: readonly (int) => int): int { g(g(x)) }`. -/
def twice : Fn :=
  { owns := [("x", .int)], refs := [("g", .ro, .fn .shared .int .int [])], ret := .int, row := [],
    body := .let_ "t" .int (.apply .shared (var "g") (.read (var "x"))) (.apply .shared (var "g") (.read (var "t"))) }

/-- `let b = Box.new(20); let u = { const f = (x) => x + *b; twice(2, f) }; u + *b`: the closure reads
`b`, lent on to `twice`, while `b` is only read; once it is gone, `b` is whole again; 62, and nothing
left allocated. -/
def higher : Expr :=
  .let_ "b" (.box .int) (.new (.lit 20))
    (.let_ "u" .int (.lendClo "f" 0 (var "b") (.call 1 [.lit 2] [(.ro, var "f")]))
      (.add (.read (var "u")) (.read (deref (var "b")))))

example : value (eval [addTo, twice] [] 30 [] .empty [] higher) = some 62 := by
  run [higher, addTo, twice, cloFn]
example : freed (eval [addTo, twice] [] 30 [] .empty [] higher) := by
  run [higher, addTo, twice, cloFn]

theorem higher_fns_ok : FnsOk [addTo, twice] [] := by
  intro d hd
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact ⟨by decide, by decide, _, .add (.read (.own rfl)) (.read (.deref (.ref (m := .ro) rfl)))⟩
  · exact ⟨by decide, _, .let_ (live := true) rfl
      (.applyBorrow (by decide) (.read (.own rfl)) (.ref (m := .ro) rfl) (fun h => by cases h) (by simp))
      (.applyBorrow (by decide) (.read (.own rfl)) (.ref (m := .ro) rfl) (fun h => by cases h) (by simp))⟩

theorem higher_typed : Typed [addTo, twice] [] [] higher .int [] [.fail] := by
  have hcall : Typed [addTo, twice] [] [("f", .ref .ro (.fn .shared .int .int [])), ("b", .ref .ro (.box .int))]
      (.call 1 [.lit 2] [(.ro, var "f")]) .int
      [("f", .ref .ro (.fn .shared .int .int [])), ("b", .ref .ro (.box .int))] [.fail] :=
    .call (d := twice) rfl rfl rfl (by simp [twice]) (.cons .lit .nil)
      (.cons (.ref (m := .ro) rfl) (fun h => by cases h) rfl .nil) (by simp [LentApart])
  have hlc := Typed.lendClo (F := [addTo, twice]) (O := []) (Γ := [("b", .own (.box .int) true)]) (f := 0)
    (d := addTo) (p := var "b") (y := "b") (x := "f") (r := [.fail]) (τb := .int)
    (Γb := [("b", .ref .ro (.box .int))]) rfl rfl rfl rfl rfl rfl (.own rfl) rfl
    (by simpa [addTo, freeze, Slot.ro] using hcall)
  simp only [thaw] at hlc
  exact .let_ (live := true) rfl (.new .lit) (.let_ (live := true) rfl (by simpa using hlc)
    (.add (.read (.own rfl)) (.read (.deref (.own rfl)))))

example : ∀ n, match eval [addTo, twice] [] n [.abort .fail 0] .empty [] higher with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT [addTo, twice] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok higher_fns_ok higher_typed

/-! A closure over a `mut` borrow, and a function that takes one `mut`. -/

/-- `function callsTwice(g: mut (int) => int): int { g(1); g(2) }`. -/
def callsTwice : Fn :=
  { owns := [], refs := [("g", .mut, .fn .excl .int .int [])], ret := .int, row := [],
    body := .let_ "t" .int (.apply .excl (var "g") (.lit 1)) (.apply .excl (var "g") (.lit 2)) }

/-- `let b = Box.new(10); let u = { const f = (x) => { *b = *b + x; *b }; callsTwice(f) }; u + *b`:
the closure changes `b`, lent on `mut` to `callsTwice`, while `b` is out of reach; once it is gone,
`b` is whole again, and holds what the closure left: 13 + 13, and nothing left allocated. -/
def tally : Expr :=
  .let_ "b" (.box .int) (.new (.lit 10))
    (.let_ "u" .int (.lendClo "f" 0 (var "b") (.call 1 [] [(.mut, var "f")]))
      (.add (.read (var "u")) (.read (deref (var "b")))))

example : value (eval [bump, callsTwice] [] 30 [] .empty [] tally) = some 26 := by
  run [tally, bump, callsTwice, cloFn]
example : freed (eval [bump, callsTwice] [] 30 [] .empty [] tally) := by
  run [tally, bump, callsTwice, cloFn]

theorem tally_fns_ok : FnsOk [bump, callsTwice] [] := by
  intro d hd
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact ⟨by decide, by decide, _, .let_ (live := true) rfl
      (.add (.read (.deref (.ref (m := .mut) rfl))) (.read (.own rfl)))
      (.let_ (live := true) rfl (.write (.read (.own rfl)) (.deref (.ref (m := .mut) rfl)))
        (.atom (.read (.deref (.ref (m := .mut) rfl)))))⟩
  · exact ⟨by decide, _, .let_ (live := true) rfl
      (.applyBorrow (by decide) .lit (.ref (m := .mut) rfl) (fun _ => rfl) (by simp))
      (.applyBorrow (by decide) .lit (.ref (m := .mut) rfl) (fun _ => rfl) (by simp))⟩

theorem tally_typed : Typed [bump, callsTwice] [] [] tally .int [] [.fail] := by
  have hcall : Typed [bump, callsTwice] [] [("f", .ref .mut (.fn .excl .int .int [])), ("b", .lent (.box .int))]
      (.call 1 [] [(.mut, var "f")]) .int
      [("f", .ref .mut (.fn .excl .int .int [])), ("b", .lent (.box .int))] [.fail] :=
    .call (d := callsTwice) rfl rfl rfl (by simp [callsTwice]) .nil
      (.cons (.ref (m := .mut) rfl) (fun _ => rfl) rfl .nil) (by simp [LentApart])
  have hlc := Typed.lendCloMut (F := [bump, callsTwice]) (O := []) (Γ := [("b", .own (.box .int) true)]) (f := 0)
    (d := bump) (p := var "b") (y := "b") (x := "f") (r := [.fail]) (τb := .int)
    (Γb := [("b", .lent (.box .int))]) rfl rfl rfl rfl rfl rfl (.own rfl) (fun _ _ _ h => by simp [lookup] at h) rfl
    (by simpa [bump, hide, Slot.ty] using hcall)
  simp only [thaw] at hlc
  exact .let_ (live := true) rfl (.new .lit) (.let_ (live := true) rfl (by simpa using hlc)
    (.add (.read (.own rfl)) (.read (.deref (.own rfl)))))

example : ∀ n, match eval [bump, callsTwice] [] n [.abort .fail 0] .empty [] tally with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT [bump, callsTwice] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok tally_fns_ok tally_typed

theorem placeTy_var_root {w : Bool} (h : PlaceTy Γ (.var x) τ w y) : y = x := by
  cases h <;> rfl

/-- `{ const f = (x) => { … }; f = …; }` over a borrow of `b`: putting another closure in place
of one borrowed `mut`, the types reject it. -/
def swapClosure : Expr :=
  .lendClo "f" 0 (var "b") (.assign (var "f") (.fn .excl .int .int []) (.lit 0))

theorem swapClosure_rejected : ¬ Typed [bump] [] [("b", .own (.box .int) true)] swapClosure τ Γ' r := by
  intro h
  cases h with
  | lendClo hfd hcap => simp at hfd; subst hfd; simp [bump] at hcap
  | lendCloMut _ _ _ _ _ _ _ _ _ hb =>
    cases hb with
    | assign _ hp hsh =>
      obtain rfl := placeTy_var_root hp
      simp [lookup, Slot.shell] at hsh

/-! Closures returned and passed by value. -/

/-- `function make(b: Box<int>): once (int) => int { (x) => *b + x }`: a closure that owns the box. -/
def make : Fn :=
  { owns := [("b", .box .int)], refs := [], ret := .fn .once .int .int [], row := [],
    body := .lam 0 (.move "b") }

/-- `function useOnce(g: once (int) => int): int { g(5) }`. -/
def useOnce : Fn :=
  { owns := [("g", .fn .once .int .int [])], refs := [], ret := .int, row := [],
    body := .apply .once (var "g") (.lit 5) }

/-- `let b = Box.new(40); let f = make(b); useOnce(f)`: the box goes into the closure `make` returns,
and the closure into `useOnce`, which consumes it; 45, and nothing left allocated. -/
def handOff : Expr :=
  .let_ "b" (.box .int) (.new (.lit 40))
    (.let_ "f" (.fn .once .int .int []) (.call 1 [.move "b"] []) (.call 2 [.move "f"] []))

example : value (eval [spend, make, useOnce] [] 30 [] .empty [] handOff) = some 45 := by
  run [handOff, spend, make, useOnce, cloFn]
example : freed (eval [spend, make, useOnce] [] 30 [] .empty [] handOff) := by
  run [handOff, spend, make, useOnce, cloFn]

theorem handOff_fns_ok : FnsOk [spend, make, useOnce] [] := by
  intro d hd
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨by decide, by decide, _, .add (.read (.deref (.own rfl))) (.read (.own rfl))⟩
  · exact ⟨by decide, _, .lam (d := spend) rfl rfl rfl rfl rfl (.move rfl rfl)⟩
  · exact ⟨by decide, _, .applyOnce rfl (by simp) .lit⟩

theorem handOff_typed : Typed [spend, make, useOnce] [] [] handOff .int [] [.fail] :=
  .let_ (live := false) rfl (.new .lit)
    (.let_ (live := false) rfl (.call (d := make) rfl rfl rfl (by simp [make]) (.cons (.move rfl rfl) .nil) .nil
        (by simp [LentApart]))
      (.call (d := useOnce) rfl rfl rfl (by simp [useOnce]) (.cons (.move rfl rfl) .nil) .nil (by simp [LentApart])))

example : ∀ n, match eval [spend, make, useOnce] [] n [.abort .fail 0] .empty [] handOff with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT [spend, make, useOnce] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok handOff_fns_ok handOff_typed

/-! A closure that owns a closure. -/

/-- `(x) => x + *c`, owning a box `c`, called through a borrow. -/
def addBox : Fn :=
  { owns := [("x", .int)], refs := [], ret := .int, row := [],
    body := .add (.read (var "x")) (.read (deref (var "c"))), cap := some ("c", .box .int, .shared) }

/-- `(x) => g(g(x))`, owning a closure `g`. -/
def twiceOf : Fn :=
  { owns := [("x", .int)], refs := [], ret := .int, row := [],
    body := .let_ "t" .int (.apply .shared (var "g") (.read (var "x"))) (.apply .shared (var "g") (.read (var "t"))),
    cap := some ("g", .fn .shared .int .int [], .shared) }

/-- `let b = Box.new(5); let f = (x) => x + *b; let h = (x) => f(f(x)); h(1)`: `h` takes `f`, which
took `b`; 11, and dropping `h` drops `f` and its box: nothing left allocated. -/
def nested : Expr :=
  .let_ "b" (.box .int) (.new (.lit 5))
    (.let_ "f" (.fn .shared .int .int []) (.lam 0 (.move "b"))
      (.let_ "h" (.fn .shared .int .int []) (.lam 1 (.move "f")) (.apply .shared (var "h") (.lit 1))))

example : value (eval [addBox, twiceOf] [] 30 [] .empty [] nested) = some 11 := by
  run [nested, addBox, twiceOf, cloFn]
example : freed (eval [addBox, twiceOf] [] 30 [] .empty [] nested) := by
  run [nested, addBox, twiceOf, cloFn]

theorem nested_fns_ok : FnsOk [addBox, twiceOf] [] := by
  intro d hd
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact ⟨by decide, by decide, _, .add (.read (.own rfl)) (.read (.deref (.ref (m := .ro) rfl)))⟩
  · exact ⟨by decide, by decide, _, .let_ (live := true) rfl
      (.applyBorrow (by decide) (.read (.own rfl)) (.ref (m := .ro) rfl) (fun h => by cases h) (by simp))
      (.applyBorrow (by decide) (.read (.own rfl)) (.ref (m := .ro) rfl) (fun h => by cases h) (by simp))⟩

theorem nested_typed : Typed [addBox, twiceOf] [] [] nested .int [] [.fail] :=
  .let_ (live := false) rfl (.new .lit)
    (.let_ (live := false) rfl (.lam (d := addBox) rfl rfl rfl rfl rfl (.move rfl rfl))
      (.let_ (live := true) rfl (.lam (d := twiceOf) rfl rfl rfl rfl rfl (.move rfl rfl))
        (.applyBorrow (by decide) .lit (.own rfl) (fun h => by cases h) (by simp))))

example : ∀ n, match eval [addBox, twiceOf] [] n [.abort .fail 0] .empty [] nested with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT [addBox, twiceOf] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok nested_fns_ok nested_typed

/-! A borrow a function picks as it runs. -/

/-- `function either(k: int, a: mut Box<int>, b: mut Box<int>): mut int { k == 0 ? a.* : b.* }`. -/
def either : Fn :=
  { owns := [("k", .int)], refs := [("a", .mut, .box .int), ("b", .mut, .box .int)], ret := .int, row := [],
    body := .atom (.read (var "k")), retp := some (.mut, [(0, deref (var "a")), (1, deref (var "b"))]) }

/-- `let a = Box.new(1); let b = Box.new(2); { const v = either(1, mut a, mut b); v = 10 }; *a + *b`:
which box the borrow changes, the callee picks as it runs, so neither may be reached while it lives;
1 + 10, and nothing left allocated. -/
def picks : Expr :=
  .let_ "a" (.box .int) (.new (.lit 1))
    (.let_ "b" (.box .int) (.new (.lit 2))
      (.let_ "u" .int (.lendCall "v" .mut 0 [.lit 1] [(.mut, var "a"), (.mut, var "b")] (.write (var "v") (.lit 10)))
        (.add (.read (deref (var "a"))) (.read (deref (var "b"))))))

example : value (eval [either] [] 30 [] .empty [] picks) = some 11 := by
  run [picks, either]
example : freed (eval [either] [] 30 [] .empty [] picks) := by
  run [picks, either]

theorem either_ok : FnsOk [either] [] := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  refine ⟨by decide, by simp, _, .atom (.read (.own rfl)), fun c hc => ?_⟩
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨"a", .mut, .box .int, true, rfl, .deref (.ref (m := .mut) rfl), fun _ => rfl⟩
  · exact ⟨"b", .mut, .box .int, true, rfl, .deref (.ref (m := .mut) rfl), fun _ => rfl⟩

theorem picks_typed : Typed [either] [] [] picks .int [] [.fail] := by
  have := Typed.lendCall (F := [either]) (O := []) (Γ := [("b", .own (.box .int) true), ("a", .own (.box .int) true)])
    (f := 0) (d := either) (m := .mut) (cs := [(0, deref (var "a")), (1, deref (var "b"))]) (r := [.fail])
    (owned := [.lit 1]) (Γ₁ := [("b", .own (.box .int) true), ("a", .own (.box .int) true)])
    (lent := [(.mut, var "a"), (.mut, var "b")]) (ys := [(.mut, "a"), (.mut, "b")]) (zs := ["a", "b"]) (x := "v")
    (body := .write (var "v") (.lit 10)) (τb := .int) (Γb := [("b", .lent (.box .int)), ("a", .lent (.box .int))])
    rfl rfl rfl (by simp [either]) (.cons .lit .nil)
    (.cons (.own rfl) (fun _ => rfl) rfl (.cons (.own rfl) (fun _ => rfl) rfl .nil)) (by simp [LentApart, Place.root])
    (.cons ⟨.mut, rfl, fun _ => rfl⟩ (.cons ⟨.mut, rfl, fun _ => rfl⟩ .nil))
    (fun _ => ⟨by simp, rfl, by intro c hc e he; simp at hc; rcases hc with rfl | rfl <;> (simp [either] at he; subst he; rfl),
      fun z hz t A B h => by simp at hz; rcases hz with rfl | rfl <;> simp [lookup] at h⟩) rfl
    (.write .lit (.ref (m := .mut) rfl))
  simp only [unlend, unhideAll, thaw, hide] at this
  exact .let_ (live := true) rfl (.new .lit) (.let_ (live := true) rfl (.new .lit)
    (.let_ (live := true) rfl (by simpa using this)
      (.add (.read (.deref (.own rfl))) (.read (.deref (.own rfl))))))

example : ∀ n, match eval [either] [] n [.abort .fail 0] .empty [] picks with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT [either] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok either_ok picks_typed

/-! Pairs, and a borrow of one field. -/

/-- `function inc(r: mut int): int { r = r + 1; r }`. -/
def inc : Fn :=
  { owns := [], refs := [("r", .mut, .int)], ret := .int, row := [],
    body := .let_ "t" .int (.add (.read (var "r")) (.lit 1))
      (.let_ "u" .int (.write (var "r") (.read (var "t"))) (.atom (.read (var "r")))) }

/-- `let p = [1, 40]; inc(mut p[0]); p[0] + p[1]`: the call borrows one field of the pair and leaves
the other as it is; 42, and nothing left allocated. -/
def fields : Expr :=
  .let_ "p" (.pair .int .int) (.pair (.lit 1) (.lit 40))
    (.let_ "u" .int (.call 0 [] [(.mut, .fst (var "p"))])
      (.add (.read (.fst (var "p"))) (.read (.snd (var "p")))))

example : value (eval [inc] [] 30 [] .empty [] fields) = some 42 := by
  run [fields, inc]
example : freed (eval [inc] [] 30 [] .empty [] fields) := by
  run [fields, inc]

theorem inc_ok : FnsOk [inc] [] := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  exact ⟨by decide, _, .let_ (live := true) rfl (.add (.read (.ref (m := .mut) rfl)) .lit)
    (.let_ (live := true) rfl (.write (.read (.own rfl)) (.ref (m := .mut) rfl)) (.atom (.read (.ref (m := .mut) rfl))))⟩

theorem fields_typed : Typed [inc] [] [] fields .int [] [.fail] :=
  .let_ (live := true) rfl (.pair .lit .lit)
    (.let_ (live := true) rfl
      (.call (d := inc) rfl rfl rfl (by simp [inc]) .nil (.cons (.fst (.own rfl)) (fun _ => rfl) rfl .nil)
        (by simp [LentApart]))
      (.add (.read (.fst (.own rfl))) (.read (.snd (.own rfl)))))

example : ∀ n, match eval [inc] [] n [.abort .fail 0] .empty [] fields with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT [inc] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok inc_ok fields_typed

/-! Fields of one pair lent to one call together: both `mut`, or one `mut` and one `readonly`. -/

/-- `function swap(a: mut int, b: mut int): int { const t = a; a = b; b = t; 0 }`. -/
def swap : Fn :=
  { owns := [], refs := [("a", .mut, .int), ("b", .mut, .int)], ret := .int, row := [],
    body := .let_ "t" .int (.atom (.read (var "a")))
      (.let_ "u" .int (.write (var "a") (.read (var "b")))
        (.let_ "w" .int (.write (var "b") (.read (var "t"))) (.atom (.lit 0)))) }

/-- `function addField(a: mut int, b: int): int { a = a + b; 0 }`. -/
def addField : Fn :=
  { owns := [], refs := [("a", .mut, .int), ("b", .ro, .int)], ret := .int, row := [],
    body := .let_ "t" .int (.add (.read (var "a")) (.read (var "b")))
      (.let_ "u" .int (.write (var "a") (.read (var "t"))) (.atom (.lit 0))) }

/-- `let p = [2, 40]; swap(mut p[0], mut p[1]); addField(mut p[0], p[1]); p[0] + p[1]`: each call holds
both fields at once, apart; 44, and nothing left allocated. -/
def fieldPairs : Expr :=
  .let_ "p" (.pair .int .int) (.pair (.lit 2) (.lit 40))
    (.let_ "u" .int (.call 0 [] [(.mut, .fst (var "p")), (.mut, .snd (var "p"))])
      (.let_ "w" .int (.call 1 [] [(.mut, .fst (var "p")), (.ro, .snd (var "p"))])
        (.add (.read (.fst (var "p"))) (.read (.snd (var "p"))))))

example : value (eval [swap, addField] [] 30 [] .empty [] fieldPairs) = some 44 := by
  run [fieldPairs, swap, addField]
example : freed (eval [swap, addField] [] 30 [] .empty [] fieldPairs) := by
  run [fieldPairs, swap, addField]

theorem swap_ok : FnsOk [swap, addField] [] := by
  intro d hd
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact ⟨by decide, _, .let_ (live := true) rfl (.atom (.read (.ref (m := .mut) rfl)))
      (.let_ (live := true) rfl (.write (.read (.ref (m := .mut) rfl)) (.ref (m := .mut) rfl))
        (.let_ (live := true) rfl (.write (.read (.own rfl)) (.ref (m := .mut) rfl)) (.atom .lit)))⟩
  · exact ⟨by decide, _, .let_ (live := true) rfl (.add (.read (.ref (m := .mut) rfl)) (.read (.ref (m := .ro) rfl)))
      (.let_ (live := true) rfl (.write (.read (.own rfl)) (.ref (m := .mut) rfl)) (.atom .lit))⟩

theorem fieldPairs_typed : Typed [swap, addField] [] [] fieldPairs .int [] [.fail] :=
  .let_ (live := true) rfl (.pair .lit .lit)
    (.let_ (live := true) rfl
      (.call (d := swap) rfl rfl rfl (by simp [swap]) .nil
        (.cons (.fst (.own rfl)) (fun _ => rfl) rfl (.cons (.snd (.own rfl)) (fun _ => rfl) rfl .nil))
        (by simp [LentApart, Place.apart_fields]))
      (.let_ (live := true) rfl
        (.call (d := addField) rfl rfl rfl (by simp [addField]) .nil
          (.cons (.fst (.own rfl)) (fun _ => rfl) rfl (.cons (.snd (.own rfl)) (fun _ => rfl) rfl .nil))
          (by simp [LentApart, Place.apart_fields]))
        (.add (.read (.fst (.own rfl))) (.read (.snd (.own rfl))))))

example : ∀ n, match eval [swap, addField] [] n [.abort .fail 0] .empty [] fieldPairs with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT [swap, addField] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok swap_ok fieldPairs_typed

/-- `swap(mut p[0], mut p[0])`: one field lent `mut` twice is rejected. -/
theorem sameField_rejected : ¬ LentApart [(.mut, .fst (var "p")), (.mut, .fst (var "p"))] := by
  intro h
  simp [LentApart, Place.root] at h
  obtain ⟨r, ⟨-, h⟩ | ⟨h, -⟩⟩ := h <;> (cases h with | fst h => cases h)

/-! A field borrowed for a while, the field beside it read and changed meanwhile. -/

/-- `let p = [1, 40]; { const r = mut p[0]; r = r + p[1]; p[1] = 2; } p[0] + p[1]`: while `r` borrows
the first field, the second is read and written; 43, and nothing left allocated. -/
def fieldBorrow : Expr :=
  .let_ "p" (.pair .int .int) (.pair (.lit 1) (.lit 40))
    (.let_ "u" .int (.lend "r" .mut (fieldOf true "p")
        (.let_ "t" .int (.add (.read (var "r")) (.read (.snd (var "p"))))
          (.let_ "v" .int (.write (var "r") (.read (var "t")))
            (.write (.snd (var "p")) (.lit 2)))))
      (.add (.read (.fst (var "p"))) (.read (.snd (var "p")))))

example : value (eval [] [] 30 [] .empty [] fieldBorrow) = some 43 := by
  run [fieldBorrow, fieldOf]
example : freed (eval [] [] 30 [] .empty [] fieldBorrow) := by
  run [fieldBorrow, fieldOf]

theorem fieldBorrow_typed : Typed [] [] [] fieldBorrow .int [] [.fail] := by
  have hbody : Typed [] [] [("r", .ref .mut .int), ("p", .half true .int .int)]
      (.let_ "t" .int (.add (.read (var "r")) (.read (.snd (var "p"))))
        (.let_ "v" .int (.write (var "r") (.read (var "t"))) (.write (.snd (var "p")) (.lit 2))))
      .int [("r", .ref .mut .int), ("p", .half true .int .int)] [.fail] :=
    .let_ (live := true) rfl (.add (.read (.ref (m := .mut) rfl)) (.read (.snd (.half rfl rfl))))
      (.let_ (live := true) rfl (.write (.read (.own rfl)) (.ref (m := .mut) rfl))
        (.write .lit (.snd (.half rfl rfl))))
  have hlend := Typed.lendField (F := []) (O := []) (Γ := [("p", .own (.pair .int .int) true)]) (x := "r") (y := "p")
    (s := .own (.pair .int .int) true) (A := .int) (B := .int) (t := true) (m := .mut) (r := [.fail])
    (Γb := [("p", .half true .int .int)]) rfl rfl rfl (.inl ⟨_, rfl⟩) rfl (fun _ => rfl)
    (by simpa [setSlot] using hbody)
  simp only [thaw] at hlend
  exact .let_ (live := true) rfl (.pair .lit .lit)
    (.let_ (live := true) rfl (by simpa using hlend)
      (.add (.read (.fst (.own rfl))) (.read (.snd (.own rfl)))))

example : ∀ n, match eval [] [] n [.abort .fail 0] .empty [] fieldBorrow with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (fun _ h => by simp at h) fieldBorrow_typed

/-! Tags, and matching them. -/

/-- `let b = Box.new(5); let v: #L(int) | #R(Box<int>) = #R(b); match (v) { #L(y) => y, #R(y) => *y }`:
the arm owns the box the tag carried and drops it as it ends; 5, and nothing left allocated. -/
def tags : Expr :=
  .let_ "b" (.box .int) (.new (.lit 5))
    (.let_ "v" (.sum .int (.box .int)) (.inj .int (.box .int) false (.move "b"))
      (.case "v" "y" .int (.box .int) (.atom (.read (var "y"))) (.atom (.read (deref (var "y"))))))

example : value (eval [] [] 30 [] .empty [] tags) = some 5 := by
  run [tags]
example : freed (eval [] [] 30 [] .empty [] tags) := by
  run [tags]

theorem tags_typed : Typed [] [] [] tags .int [] [.fail] :=
  .let_ (live := false) rfl (.new .lit)
    (.let_ (live := false) rfl (.inj (t := false) (.move rfl rfl) rfl)
      (.case rfl rfl rfl (l₁ := true) (l₂ := true) (.atom (.read (.own rfl))) (.atom (.read (.deref (.own rfl))))
        (Weaker.refl _) (Weaker.refl _)))

example : ∀ n, match eval [] [] n [.abort .fail 0] .empty [] tags with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (by intro d hd; simp at hd) tags_typed

/-- `let v = #L(1); match (mut v) { #L(x) => x = 41, #R(x) => x = 0 }; match (v) { #L(y) => y, #R(y) => y }`:
an arm changes what the tag carries through a `mut` borrow; 41. -/
def tagRef : Expr :=
  .let_ "v" (.sum .int .int) (.inj .int .int true (.lit 1))
    (.let_ "u" .int (.caseRef "x" .mut (var "v") (.write (var "x") (.lit 41)) (.write (var "x") (.lit 0)))
      (.case "v" "y" .int .int (.atom (.read (var "y"))) (.atom (.read (var "y")))))

example : value (eval [] [] 30 [] .empty [] tagRef) = some 41 := by
  run [tagRef]
example : freed (eval [] [] 30 [] .empty [] tagRef) := by
  run [tagRef]

theorem tagRef_typed : Typed [] [] [] tagRef .int [] [.fail] := by
  have := Typed.caseRef (F := []) (O := []) (Γ := [("v", .own (.sum .int .int) true)]) (x := "x") (m := .mut)
    (p := var "v") (A := .int) (B := .int) (w := true) (y := "v") (τ := .int) (r := [.fail])
    (e₁ := .write (var "x") (.lit 41)) (e₂ := .write (var "x") (.lit 0))
    (Γb₁ := [("v", .lent (.sum .int .int))]) (Γb₂ := [("v", .lent (.sum .int .int))])
    (Γb := [("v", .lent (.sum .int .int))]) rfl (.own rfl) (fun _ _ _ h => by simp [lookup] at h) (fun _ => rfl)
    (fun _ => ⟨rfl, rfl⟩)
    (.write .lit (.ref (m := .mut) rfl)) (.write .lit (.ref (m := .mut) rfl)) (Weaker.refl _) (Weaker.refl _)
  simp only [thaw] at this
  exact .let_ (live := false) rfl (.inj (t := true) .lit rfl)
    (.let_ (live := true) rfl (by simpa using this)
      (.case rfl rfl rfl (l₁ := true) (l₂ := true) (.atom (.read (.own rfl))) (.atom (.read (.own rfl)))
        (Weaker.refl _) (Weaker.refl _)))

example : ∀ n, match eval [] [] n [.abort .fail 0] .empty [] tagRef with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (by intro d hd; simp at hd) tagRef_typed

end FlyCore.Ownership.Examples
