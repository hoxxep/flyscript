import FlyCore.OwnershipMain

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
      cleanA, dropRet, armEnd, callRet, allocAll, dropCells, dropCell, drop, dropK, pick, Store.fresh, Store.alloc, Store.set, find,
      Frame.handles, Kont.push, lookup, Res.done, Outcome.res, Cap.at, Store.empty, Store.sched0, value, freed, freedBelow,
      Store.tag, Store.freeAll, Store.moveAll, dropCellsWith,
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
    have := Typed.call (k := 0) (F := [addInto]) (O := []) (Γ := [("y", .own (.box .int) true), ("x", .own (.box .int) true)])
      (f := 0) (d := addInto) (ys := [(.mut, "x")]) (r := [.fail]) rfl rfl rfl (by simp [addInto])
      (.cons (.move (x := "y") rfl rfl) .nil) (.cons (.own (by simp [lookup, setSlot])) (fun _ => rfl) rfl .nil)
      (by simp [LentApart])
    simpa [setSlot, addInto] using this
  exact .let_ rfl (.new .lit) (.let_ rfl (.new .lit) hc)

example : ∀ n, match eval [addInto] [] n [.abort .fail 0] .empty [] lends with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [addInto] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
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
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
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
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
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
    (τ := .int) (Γb := [("n", .lent .int false)])
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
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
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
theorem lent_unreachable (h : lookup x Γ = some (.lent τ' hd)) : ¬ PlaceTy Γ (var x) τ w y := by
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
          exact lent_unreachable (τ' := .int) (hd := false) (by decide) hq

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
    (Γb := [("x", .lent (.box .int) false)]) rfl (.deref (.own rfl)) (fun _ => rfl) (fun _ => rfl)
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
        | read hq | readRef hq =>
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
    (τb := .int) (Γb := [("x", .lent (.box .int) false)])
    rfl rfl rfl (by simp [inside]) .nil (.cons (.own rfl) (fun _ => rfl) rfl .nil) (by simp [LentApart])
    (.cons ⟨.mut, rfl, fun _ => rfl⟩ .nil)
    (fun _ => ⟨by simp, rfl, by simp [inside, Ty.shell], fun z hz t A B h => by simp at hz; subst hz; simp [lookup] at h⟩) rfl
    (.let_ (live := true) rfl (.add (.read (.ref rfl)) .lit) (.write (.read (.own rfl)) (.ref (m := .mut) rfl)))
  simp only [unlend, unhideAll, thaw] at this
  exact .let_ (live := true) rfl (.new .lit) (.let_ (live := true) rfl (by simpa using this)
    (.atom (.read (.deref (.own rfl)))))

example : ∀ n, match eval [inside] [] n [.abort .fail 0] .empty [] returns with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [inside] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
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
          | read hq | readRef hq =>
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
      (r := [.fail]) rfl rfl rfl rfl rfl (.move (x := "b") rfl rfl) rfl
    simpa [bump, setSlot] using this
  exact .let_ (live := false) rfl (.new .lit)
    (.let_ (live := true) rfl hlam
      (.let_ (live := true) rfl (.applyBorrow (by decide) .lit (.own rfl) (fun _ => rfl) (by simp))
        (.applyBorrow (by decide) .lit (.own rfl) (fun _ => rfl) (by simp))))

example : ∀ n, match eval [bump] [] n [.abort .fail 0] .empty [] counter with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [bump] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
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
    .call (k := 0) (d := twice) rfl rfl rfl (by simp [twice]) (.cons .lit .nil)
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
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [addTo, twice] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
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
  have hcall : Typed [bump, callsTwice] [] [("f", .ref .mut (.fn .excl .int .int [])), ("b", .lent (.box .int) false)]
      (.call 1 [] [(.mut, var "f")]) .int
      [("f", .ref .mut (.fn .excl .int .int [])), ("b", .lent (.box .int) false)] [.fail] :=
    .call (k := 0) (d := callsTwice) rfl rfl rfl (by simp [callsTwice]) .nil
      (.cons (.ref (m := .mut) rfl) (fun _ => rfl) rfl .nil) (by simp [LentApart])
  have hlc := Typed.lendCloMut (F := [bump, callsTwice]) (O := []) (Γ := [("b", .own (.box .int) true)]) (f := 0)
    (d := bump) (p := var "b") (y := "b") (x := "f") (r := [.fail]) (τb := .int)
    (Γb := [("b", .lent (.box .int) false)]) rfl rfl rfl rfl rfl rfl (.own rfl) (fun _ _ _ h => by simp [lookup] at h) rfl
    (by simpa [bump, hide, Slot.ty, Slot.shell] using hcall)
  simp only [thaw] at hlc
  exact .let_ (live := true) rfl (.new .lit) (.let_ (live := true) rfl (by simpa using hlc)
    (.add (.read (.own rfl)) (.read (.deref (.own rfl)))))

example : ∀ n, match eval [bump, callsTwice] [] n [.abort .fail 0] .empty [] tally with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [bump, callsTwice] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
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
      rcases var_writable hp rfl with h | h | ⟨_, _, _, h⟩
      · simp [lookup] at h
      · have := hsh _ h; simp [Ty.shell] at this
      · simp [lookup] at h

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
  · exact ⟨by decide, _, .lam (d := spend) rfl rfl rfl rfl rfl (.move rfl rfl) rfl⟩
  · exact ⟨by decide, _, .applyOnce rfl (by simp) .lit⟩

theorem handOff_typed : Typed [spend, make, useOnce] [] [] handOff .int [] [.fail] :=
  .let_ (live := false) rfl (.new .lit)
    (.let_ (live := false) rfl (.call (k := 0) (d := make) rfl rfl rfl (by simp [make]) (.cons (.move rfl rfl) .nil) .nil
        (by simp [LentApart]))
      (.call (k := 0) (d := useOnce) rfl rfl rfl (by simp [useOnce]) (.cons (.move rfl rfl) .nil) .nil (by simp [LentApart])))

example : ∀ n, match eval [spend, make, useOnce] [] n [.abort .fail 0] .empty [] handOff with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [spend, make, useOnce] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
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
    (.let_ (live := false) rfl (.lam (d := addBox) rfl rfl rfl rfl rfl (.move rfl rfl) rfl)
      (.let_ (live := true) rfl (.lam (d := twiceOf) rfl rfl rfl rfl rfl (.move rfl rfl) rfl)
        (.applyBorrow (by decide) .lit (.own rfl) (fun h => by cases h) (by simp))))

example : ∀ n, match eval [addBox, twiceOf] [] n [.abort .fail 0] .empty [] nested with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [addBox, twiceOf] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
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
    (body := .write (var "v") (.lit 10)) (τb := .int) (Γb := [("b", .lent (.box .int) false), ("a", .lent (.box .int) false)])
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
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [either] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
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
      (.call (k := 0) (d := inc) rfl rfl rfl (by simp [inc]) .nil (.cons (.fst (.own rfl)) (fun _ => rfl) rfl .nil)
        (by simp [LentApart]))
      (.add (.read (.fst (.own rfl))) (.read (.snd (.own rfl)))))

example : ∀ n, match eval [inc] [] n [.abort .fail 0] .empty [] fields with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [inc] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
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
      (.call (k := 0) (d := swap) rfl rfl rfl (by simp [swap]) .nil
        (.cons (.fst (.own rfl)) (fun _ => rfl) rfl (.cons (.snd (.own rfl)) (fun _ => rfl) rfl .nil))
        (by simp [LentApart, Place.apart_fields]))
      (.let_ (live := true) rfl
        (.call (k := 0) (d := addField) rfl rfl rfl (by simp [addField]) .nil
          (.cons (.fst (.own rfl)) (fun _ => rfl) rfl (.cons (.snd (.own rfl)) (fun _ => rfl) rfl .nil))
          (by simp [LentApart, Place.apart_fields]))
        (.add (.read (.fst (.own rfl))) (.read (.snd (.own rfl))))))

example : ∀ n, match eval [swap, addField] [] n [.abort .fail 0] .empty [] fieldPairs with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [swap, addField] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
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
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (fun _ h => by simp at h) fieldBorrow_typed

/-- `let p = ((1, 2), 3); { const r = mut p.0.1; *r = p.0.0 + p.1 + 38 }; p.0.1`: a field two steps in
borrowed for a while, the fields beside it at each step read meanwhile — as the calculus writes it, a
borrow of the field of a borrow of a field; 42. -/
def deepField : Expr :=
  .let_ "a" (.pair .int .int) (.pair (.lit 1) (.lit 2))
    (.let_ "p" (.pair (.pair .int .int) .int) (.pair (.move "a") (.lit 3))
      (.let_ "u" .int
        (.lend "q" .mut (fieldOf true "p")
          (.lend "r" .mut (fieldOf false "q")
            (.let_ "s" .int (.add (.read (.fst (var "q"))) (.read (.snd (var "p"))))
              (.let_ "t" .int (.add (.read (var "s")) (.lit 38))
                (.write (var "r") (.read (var "t")))))))
        (.atom (.read (.snd (.fst (var "p")))))))

example : value (eval [] [] 40 [] .empty [] deepField) = some 42 := by
  run [deepField, fieldOf]
example : freed (eval [] [] 40 [] .empty [] deepField) := by
  run [deepField, fieldOf]

theorem deepField_typed : Typed [] [] [] deepField .int [] [.fail] := by
  have hin : Typed [] [] [("r", .ref .mut .int), ("q", .half false .int .int), ("p", .half true (.pair .int .int) .int),
        ("a", .own (.pair .int .int) false)]
      (.let_ "s" .int (.add (.read (.fst (var "q"))) (.read (.snd (var "p"))))
        (.let_ "t" .int (.add (.read (var "s")) (.lit 38)) (.write (var "r") (.read (var "t")))))
      .int [("r", .ref .mut .int), ("q", .half false .int .int), ("p", .half true (.pair .int .int) .int),
        ("a", .own (.pair .int .int) false)] [.fail] :=
    .let_ (live := true) rfl (.add (.read (.fst (.half rfl rfl))) (.read (.snd (.half rfl rfl))))
      (.let_ (live := true) rfl (.add (.read (.own rfl)) .lit) (.write (.read (.own rfl)) (.ref (m := .mut) rfl)))
  have hr := Typed.lendField (F := []) (O := [])
    (Γ := [("q", .ref .mut (.pair .int .int)), ("p", .half true (.pair .int .int) .int), ("a", .own (.pair .int .int) false)])
    (x := "r") (y := "q") (s := .ref .mut (.pair .int .int)) (A := .int) (B := .int) (t := false) (m := .mut)
    (r := [.fail]) (Γb := [("q", .half false .int .int), ("p", .half true (.pair .int .int) .int), ("a", .own (.pair .int .int) false)])
    rfl rfl rfl (.inr (.inl ⟨_, rfl⟩)) rfl (fun _ => rfl) (by simpa [setSlot] using hin)
  simp only [thaw] at hr
  have hq := Typed.lendField (F := []) (O := [])
    (Γ := [("p", .own (.pair (.pair .int .int) .int) true), ("a", .own (.pair .int .int) false)])
    (x := "q") (y := "p") (s := .own (.pair (.pair .int .int) .int) true) (A := .pair .int .int) (B := .int) (t := true)
    (m := .mut) (r := [.fail]) (Γb := [("p", .half true (.pair .int .int) .int), ("a", .own (.pair .int .int) false)])
    rfl rfl rfl (.inl ⟨_, rfl⟩) rfl (fun _ => rfl) (by simpa [setSlot] using hr)
  simp only [thaw] at hq
  exact .let_ (live := false) rfl (.pair .lit .lit)
    (.let_ (live := true) rfl (.pair (.move rfl rfl) .lit)
      (.let_ (live := true) rfl (by simpa [setSlot] using hq) (.atom (.read (.snd (.fst (.own rfl)))))))

example : ∀ n, match eval [] [] n [.abort .fail 0] .empty [] deepField with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (fun _ h => by simp at h) deepField_typed

/-! An arm that resumes in its midst, and goes on after the rest of its `handle`. -/

/-- `Tick`, whose operation takes nothing and gives an integer. -/
def ticks : List Op := [{ owns := [], refs := [], ret := .int }]

/-- `function after(c: int, r: int, m: mut int): int { m = r + c; m }`: what runs once the rest of the
`handle` ends, given what the arm carried and that value. -/
def after : Fn :=
  { owns := [("c", .int), ("r", .int)], refs := [("m", .mut, .int)], ret := .int, row := [],
    body := .let_ "t" .int (.add (.read (var "r")) (.read (var "c")))
      (.let_ "u" .int (.write (var "m") (.read (var "t"))) (.atom (.read (var "m")))) }

/-- `let n = 0; handle { tick() + tick() } with Tick { tick() resumes k => { n = n + 1; const r =
k(n); after(n, r) } }`: each arm counts, resumes with the count, and once the rest of the `handle`
ends adds what it carried; the second arm's runs first. 1 + 2 = 3, then 3 + 2 = 5, then 5 + 1 = 6. -/
def tallies : Expr :=
  .let_ "n" .int (.atom (.lit 0))
    (.handleR .int
      (.let_ "a" .int (.perform 0 [] []) (.let_ "b" .int (.perform 0 [] [])
        (.add (.read (var "a")) (.read (var "b")))))
      0 [⟨"m", .mut, .int, var "n"⟩] [] []
      (.let_ "t" .int (.add (.read (var "m")) (.lit 1))
        (.let_ "u" .int (.write (var "m") (.read (var "t")))
          (.let_ "p" (.pair .int .int) (.pair (.read (var "m")) (.read (var "m")))
            (.inj (.pair .int .int) .int true (.move "p")))))
      .int 0)

example : value (eval [after] ticks 60 [] .empty [] tallies) = some 6 := by
  run [tallies, after, ticks]
example : freed (eval [after] ticks 60 [] .empty [] tallies) := by
  run [tallies, after, ticks]

theorem after_ok : FnsOk [after] ticks := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  exact ⟨by decide, _, .let_ (live := true) rfl (.add (.read (.own rfl)) (.read (.own rfl)))
    (.let_ (live := true) rfl (.write (.read (.own rfl)) (.ref (m := .mut) rfl)) (.atom (.read (.ref (m := .mut) rfl))))⟩

theorem tallies_typed : Typed [after] ticks [] tallies .int [] [.fail] := by
  have harm : Typed [after] ticks (armCtx [] [] ticks[0] [("m", .mut, .int)])
      (.let_ "t" .int (.add (.read (var "m")) (.lit 1))
        (.let_ "u" .int (.write (var "m") (.read (var "t")))
          (.let_ "p" (.pair .int .int) (.pair (.read (var "m")) (.read (var "m")))
            (.inj (.pair .int .int) .int true (.move "p")))))
      (.sum (.pair .int .int) .int) [("m", .ref .mut .int)] [.fail] :=
    .let_ (live := true) rfl (.add (.read (.ref (m := .mut) rfl)) .lit)
      (.let_ (live := true) rfl (.write (.read (.own rfl)) (.ref (m := .mut) rfl))
        (.let_ (live := false) rfl (.pair (.read (.ref (m := .mut) rfl)) (.read (.ref (m := .mut) rfl)))
          (.inj (t := true) (.move rfl rfl) rfl)))
  have hbody : Typed [after] ticks [("n", .lent .int false)]
      (.let_ "a" .int (.perform 0 [] []) (.let_ "b" .int (.perform 0 [] [])
        (.add (.read (var "a")) (.read (var "b")))))
      .int [("n", .lent .int false)] [.eff 0, .fail] :=
    .let_ (live := true) rfl (.perform (op := ticks[0]) rfl (List.mem_cons_self ..) .nil .nil List.Pairwise.nil)
      (.let_ (live := true) rfl (.perform (op := ticks[0]) rfl (List.mem_cons_self ..) .nil .nil List.Pairwise.nil)
        (.add (.read (.own rfl)) (.read (.own rfl))))
  have h := Typed.handleR (F := [after]) (O := ticks) (Γ := [("n", .own .int true)]) (e := 0) (op := ticks[0])
    (caps := [⟨"m", .mut, .int, var "n"⟩]) (os := []) (rs := []) (ys := [(.mut, "n")]) (f := 0) (d := after) (C := .int)
    (τ := .int) (r := [.fail]) (Γa := [("m", .ref .mut .int)]) (Γb := [("n", .lent .int false)])
    (arm := .let_ "t" .int (.add (.read (var "m")) (.lit 1))
        (.let_ "u" .int (.write (var "m") (.read (var "t")))
          (.let_ "p" (.pair .int .int) (.pair (.read (var "m")) (.read (var "m")))
            (.inj (.pair .int .int) .int true (.move "p")))))
    (body := .let_ "a" .int (.perform 0 [] []) (.let_ "b" .int (.perform 0 [] [])
        (.add (.read (var "a")) (.read (var "b")))))
    rfl (by simp [ticks]) rfl rfl (.mut (.own rfl) rfl rfl .nil) (by simp [Exclusive]) (by decide)
    rfl rfl rfl rfl rfl rfl (by simp [after]) rfl harm (by simpa [roots, hideAll, hide, freeze, Slot.ty, Slot.shell] using hbody)
  simp only [roots, hideAll, hide, freeze, thaw, unhideAll, Slot.ty] at h
  exact .let_ (live := true) rfl (.atom .lit) (by simpa [thaw, hide, hideAll, unhideAll] using h)

example : ∀ n, match eval [after] ticks n [.abort .fail 0] .empty [] tallies with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [after] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok after_ok tallies_typed

/-- `function after2(c: int, r: int, m: mut int): int { const q = mut m; *q = r + c; *q }` -/
def after2 : Fn :=
  { owns := [("c", .int), ("r", .int)], refs := [("m", .mut, .int)], ret := .int, row := [],
    body := .lend "q" .mut (var "m") (.let_ "t" .int (.add (.read (var "r")) (.read (var "c")))
      (.let_ "u" .int (.write (var "q") (.read (var "t"))) (.atom (.read (var "q"))))) }

/-- `tallies`, its arm resuming inside a borrow of its state: `{ const q = mut n; *q = *q + 1;
const r = k(*q); *q = r + *q }`. As the calculus writes it the borrow ends where the arm resumes and is
taken again in what runs after, which reaches the same place, for the code the arm resumes cannot. -/
def tallies2 : Expr :=
  .let_ "n" .int (.atom (.lit 0))
    (.handleR .int
      (.let_ "a" .int (.perform 0 [] []) (.let_ "b" .int (.perform 0 [] [])
        (.add (.read (var "a")) (.read (var "b")))))
      0 [⟨"m", .mut, .int, var "n"⟩] [] []
      (.lend "q" .mut (var "m")
        (.let_ "t" .int (.add (.read (var "q")) (.lit 1))
          (.let_ "u" .int (.write (var "q") (.read (var "t")))
            (.let_ "p" (.pair .int .int) (.pair (.read (var "q")) (.read (var "q")))
              (.inj (.pair .int .int) .int true (.move "p"))))))
      .int 0)

example : value (eval [after2] ticks 60 [] .empty [] tallies2) = some 6 := by
  run [tallies2, after2, ticks]
example : freed (eval [after2] ticks 60 [] .empty [] tallies2) := by
  run [tallies2, after2, ticks]

theorem after2_ok : FnsOk [after2] ticks := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  refine ⟨by decide, ?_⟩
  simp only [after2, FnOk]
  have h := Typed.lend (F := [after2]) (O := ticks) (x := "q") (m := .mut) (p := var "m") (τ := .int) (y := "m")
    (Γ := fnCtx after2) (Γb := lendCtx .mut (fnCtx after2) "m") (τb := .int) (r := [])
    (body := .let_ "t" .int (.add (.read (var "r")) (.read (var "c")))
      (.let_ "u" .int (.write (var "q") (.read (var "t"))) (.atom (.read (var "q"))))) rfl (.ref (m := .mut) rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ _ _ h => by simp [fnCtx, after2, lookup] at h)
    (.let_ (live := true) rfl (.add (.read (.own rfl)) (.read (.own rfl)))
      (.let_ (live := true) rfl (.write (.read (.own rfl)) (.ref (m := .mut) rfl)) (.atom (.read (.ref (m := .mut) rfl)))))
  exact ⟨_, by simpa [fnCtx, after2] using h⟩

theorem tallies2_typed : Typed [after2] ticks [] tallies2 .int [] [.fail] := by
  have harm0 := Typed.lend (F := [after2]) (O := ticks) (x := "q") (m := .mut) (p := var "m") (τ := .int) (y := "m")
    (Γ := armCtx [] [] ticks[0] [("m", .mut, .int)]) (Γb := lendCtx .mut (armCtx [] [] ticks[0] [("m", .mut, .int)]) "m")
    (τb := .sum (.pair .int .int) .int) (r := [.fail])
    (body := .let_ "t" .int (.add (.read (var "q")) (.lit 1))
          (.let_ "u" .int (.write (var "q") (.read (var "t")))
            (.let_ "p" (.pair .int .int) (.pair (.read (var "q")) (.read (var "q")))
              (.inj (.pair .int .int) .int true (.move "p"))))) rfl (.ref (m := .mut) rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ _ _ h => by simp [armCtx, lookup] at h)
    (.let_ (live := true) rfl (.add (.read (.ref (m := .mut) rfl)) .lit)
      (.let_ (live := true) rfl (.write (.read (.own rfl)) (.ref (m := .mut) rfl))
        (.let_ (live := false) rfl (.pair (.read (.ref (m := .mut) rfl)) (.read (.ref (m := .mut) rfl)))
          (.inj (t := true) (.move rfl rfl) rfl))))
  have harm : Typed [after2] ticks (armCtx [] [] ticks[0] [("m", .mut, .int)])
      (.lend "q" .mut (var "m")
        (.let_ "t" .int (.add (.read (var "q")) (.lit 1))
          (.let_ "u" .int (.write (var "q") (.read (var "t")))
            (.let_ "p" (.pair .int .int) (.pair (.read (var "q")) (.read (var "q")))
              (.inj (.pair .int .int) .int true (.move "p"))))))
      (.sum (.pair .int .int) .int) [("m", .ref .mut .int)] [.fail] := by
    simpa [armCtx, lendCtx, hide, thaw] using harm0
  have hbody : Typed [after2] ticks [("n", .lent .int false)]
      (.let_ "a" .int (.perform 0 [] []) (.let_ "b" .int (.perform 0 [] [])
        (.add (.read (var "a")) (.read (var "b")))))
      .int [("n", .lent .int false)] [.eff 0, .fail] :=
    .let_ (live := true) rfl (.perform (op := ticks[0]) rfl (List.mem_cons_self ..) .nil .nil List.Pairwise.nil)
      (.let_ (live := true) rfl (.perform (op := ticks[0]) rfl (List.mem_cons_self ..) .nil .nil List.Pairwise.nil)
        (.add (.read (.own rfl)) (.read (.own rfl))))
  have h := Typed.handleR (F := [after2]) (O := ticks) (Γ := [("n", .own .int true)]) (e := 0) (op := ticks[0])
    (caps := [⟨"m", .mut, .int, var "n"⟩]) (os := []) (rs := []) (ys := [(.mut, "n")]) (f := 0) (d := after2) (C := .int)
    (τ := .int) (r := [.fail]) (Γa := [("m", .ref .mut .int)]) (Γb := [("n", .lent .int false)])
    (arm := .lend "q" .mut (var "m")
        (.let_ "t" .int (.add (.read (var "q")) (.lit 1))
          (.let_ "u" .int (.write (var "q") (.read (var "t")))
            (.let_ "p" (.pair .int .int) (.pair (.read (var "q")) (.read (var "q")))
              (.inj (.pair .int .int) .int true (.move "p"))))))
    (body := .let_ "a" .int (.perform 0 [] []) (.let_ "b" .int (.perform 0 [] [])
        (.add (.read (var "a")) (.read (var "b")))))
    rfl (by simp [ticks]) rfl rfl (.mut (.own rfl) rfl rfl .nil) (by simp [Exclusive]) (by decide)
    rfl rfl rfl rfl rfl rfl (by simp [after2]) rfl harm (by simpa [roots, hideAll, hide, freeze, Slot.ty, Slot.shell] using hbody)
  simp only [roots, hideAll, hide, freeze, thaw, unhideAll, Slot.ty] at h
  exact .let_ (live := true) rfl (.atom .lit) (by simpa [thaw, hide, hideAll, unhideAll] using h)

example : ∀ n, match eval [after2] ticks n [.abort .fail 0] .empty [] tallies2 with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [after2] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok after2_ok tallies2_typed


/-- `let n = 41; handle { tick() + 1000 } with Tick { tick() resumes k => { n = n + 1; n } }`: the arm
ends without resuming, so its value is the `handle`'s and the rest of the body is dropped. 42. -/
def early : Expr :=
  .let_ "n" .int (.atom (.lit 41))
    (.handleR .int
      (.let_ "a" .int (.perform 0 [] []) (.add (.read (var "a")) (.lit 1000)))
      0 [⟨"m", .mut, .int, var "n"⟩] [] []
      (.let_ "t" .int (.add (.read (var "m")) (.lit 1))
        (.let_ "u" .int (.write (var "m") (.read (var "t"))) (.inj (.pair .int .int) .int false (.read (var "m")))))
      .int 0)

example : value (eval [after] ticks 60 [] .empty [] early) = some 42 := by
  run [early, after, ticks]
example : freed (eval [after] ticks 60 [] .empty [] early) := by
  run [early, after, ticks]

theorem early_typed : Typed [after] ticks [] early .int [] [.fail] := by
  have harm : Typed [after] ticks (armCtx [] [] ticks[0] [("m", .mut, .int)])
      (.let_ "t" .int (.add (.read (var "m")) (.lit 1))
        (.let_ "u" .int (.write (var "m") (.read (var "t"))) (.inj (.pair .int .int) .int false (.read (var "m")))))
      (.sum (.pair .int .int) .int) [("m", .ref .mut .int)] [.fail] :=
    .let_ (live := true) rfl (.add (.read (.ref (m := .mut) rfl)) .lit)
      (.let_ (live := true) rfl (.write (.read (.own rfl)) (.ref (m := .mut) rfl))
        (.inj (t := false) (.read (.ref (m := .mut) rfl)) rfl))
  have hbody : Typed [after] ticks [("n", .lent .int false)]
      (.let_ "a" .int (.perform 0 [] []) (.add (.read (var "a")) (.lit 1000)))
      .int [("n", .lent .int false)] [.eff 0, .fail] :=
    .let_ (live := true) rfl (.perform (op := ticks[0]) rfl (List.mem_cons_self ..) .nil .nil List.Pairwise.nil)
      (.add (.read (.own rfl)) .lit)
  have h := Typed.handleR (F := [after]) (O := ticks) (Γ := [("n", .own .int true)]) (e := 0) (op := ticks[0])
    (caps := [⟨"m", .mut, .int, var "n"⟩]) (os := []) (rs := []) (ys := [(.mut, "n")]) (f := 0) (d := after) (C := .int)
    (τ := .int) (r := [.fail]) (Γa := [("m", .ref .mut .int)]) (Γb := [("n", .lent .int false)])
    (arm := .let_ "t" .int (.add (.read (var "m")) (.lit 1))
        (.let_ "u" .int (.write (var "m") (.read (var "t"))) (.inj (.pair .int .int) .int false (.read (var "m")))))
    (body := .let_ "a" .int (.perform 0 [] []) (.add (.read (var "a")) (.lit 1000)))
    rfl (by simp [ticks]) rfl rfl (.mut (.own rfl) rfl rfl .nil) (by simp [Exclusive]) (by decide)
    rfl rfl rfl rfl rfl rfl (by simp [after]) rfl harm (by simpa [roots, hideAll, hide, freeze, Slot.ty, Slot.shell] using hbody)
  simp only [roots, hideAll, hide, freeze, thaw, unhideAll, Slot.ty] at h
  exact .let_ (live := true) rfl (.atom .lit) (by simpa [thaw, hide, hideAll, unhideAll] using h)

example : ∀ n, match eval [after] ticks n [.abort .fail 0] .empty [] early with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [after] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok after_ok early_typed

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
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
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
    (Γb₁ := [("v", .lent (.sum .int .int) false)]) (Γb₂ := [("v", .lent (.sum .int .int) false)])
    (Γb := [("v", .lent (.sum .int .int) false)]) rfl (.own rfl) (fun _ _ _ h => by simp [lookup] at h) (fun _ => rfl)
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
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (by intro d hd; simp at hd) tagRef_typed

/-! Two tasks, each giving way where it yields, in whatever order the schedule picks. -/

/-- `Yield`, whose operation takes nothing and gives an integer. -/
def yields : List Op := [{ owns := [], refs := [], ret := .int }]

/-- `function step(k: int, b: readonly int): int { yield(); const a = k + b; yield(); a + k }` -/
def step : Fn :=
  { owns := [("k", .int)], refs := [("b", .ro, .int)], ret := .int, row := [.eff 0, .fail],
    body := .let_ "t" .int (.perform 0 [] [])
      (.let_ "a" .int (.add (.read (var "k")) (.read (var "b")))
        (.let_ "u" .int (.perform 0 [] []) (.add (.read (var "a")) (.read (var "k"))))) }

/-- `let base = 10; const [x, y] = [spawn step(1, base), spawn step(2, base)]; x + y`: 12 + 14,
whichever task the schedule runs when. -/
def tasks : Expr :=
  .let_ "base" .int (.atom (.lit 10))
    (.let_ "p" (.pair .int .int) (.par 0 0 [.lit 1] [var "base"] 0 [.lit 2] [var "base"])
      (.add (.read (.fst (var "p"))) (.read (.snd (var "p")))))

example : value (eval [step] yields 60 [] .empty [] tasks) = some 26 := by
  run [tasks, step, yields]
example : freed (eval [step] yields 60 [] .empty [] tasks) := by
  run [tasks, step, yields]
example : value (eval [step] yields 60 [] (Store.sched0 fun _ => false) [] tasks) = some 26 := by
  run [tasks, step, yields]
example : freed (eval [step] yields 60 [] (Store.sched0 fun _ => false) [] tasks) := by
  run [tasks, step, yields]

theorem step_ok : FnsOk [step] yields := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  exact ⟨by decide, _, .let_ (live := true) rfl (.perform (op := yields[0]) rfl (List.mem_cons_self ..) .nil .nil
    List.Pairwise.nil) (.let_ (live := true) rfl (.add (.read (.own rfl)) (.read (.ref (m := .ro) rfl)))
      (.let_ (live := true) rfl (.perform (op := yields[0]) rfl (List.mem_cons_self ..) .nil .nil List.Pairwise.nil)
        (.add (.read (.own rfl)) (.read (.own rfl)))))⟩

theorem tasks_typed : Typed [step] yields [] tasks .int [] [.fail] :=
  .let_ (live := true) rfl (.atom .lit)
    (.let_ (live := true) rfl (.par (op := yields[0]) (da := step) (db := step) rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl (by simp [step]) (by simp [step]) (by simp [step]) (by simp [step]) rfl rfl (.cons .lit (.cons .lit .nil))
        (.cons (.own rfl) (fun h => by cases h) rfl (.cons (.own rfl) (fun h => by cases h) rfl .nil)))
      (.add (.read (.fst (.own rfl))) (.read (.snd (.own rfl)))))

/-- Under any schedule. -/
example : ∀ s n, match eval [step] yields n [.abort .fail 0] (Store.sched0 s) [] tasks with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [step] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok_sched step_ok tasks_typed

/-- `function hold(x: Box<int>): int { yield(); yield(); *x }` -/
def hold : Fn :=
  { owns := [("x", .box .int)], refs := [], ret := .int, row := [.eff 0, .fail],
    body := .let_ "t" .int (.perform 0 [] [])
      (.let_ "u" .int (.perform 0 [] []) (.atom (.read (deref (var "x"))))) }

/-- `function failing(k: int): int { yield(); throw k }` -/
def failing : Fn :=
  { owns := [("k", .int)], refs := [], ret := .int, row := [.eff 0, .fail],
    body := .let_ "t" .int (.perform 0 [] []) (.throw_ (.read (var "k"))) }

/-- `let b = Box.new(5); try { const [x, y] = [spawn hold(b), spawn failing(7)]; x + y } catch (z) { z }`:
the second task fails, and the first, done or waiting where it gave way with the box it owns, is
dropped. 7, and nothing left allocated, under either schedule. -/
def cancel : Expr :=
  .let_ "b" (.box .int) (.new (.lit 5))
    (.try_ (.let_ "p" (.pair .int .int) (.par 0 0 [.move "b"] [] 1 [.lit 7] [])
        (.add (.read (.fst (var "p"))) (.read (.snd (var "p")))))
      "z" (.atom (.read (var "z"))))

example : value (eval [hold, failing] yields 60 [] .empty [] cancel) = some 7 := by
  run [cancel, hold, failing, yields]
example : freed (eval [hold, failing] yields 60 [] .empty [] cancel) := by
  run [cancel, hold, failing, yields]
example : value (eval [hold, failing] yields 60 [] (Store.sched0 fun _ => false) [] cancel) = some 7 := by
  run [cancel, hold, failing, yields]
example : freed (eval [hold, failing] yields 60 [] (Store.sched0 fun _ => false) [] cancel) := by
  run [cancel, hold, failing, yields]

theorem cancel_fns : FnsOk [hold, failing] yields := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact ⟨by decide, _, .let_ (live := true) rfl (.perform (op := yields[0]) rfl (List.mem_cons_self ..) .nil .nil
      List.Pairwise.nil) (.let_ (live := true) rfl (.perform (op := yields[0]) rfl (List.mem_cons_self ..) .nil .nil
        List.Pairwise.nil) (.atom (.read (.deref (.own rfl)))))⟩
  · exact ⟨by decide, _, .let_ (live := true) rfl (.perform (op := yields[0]) rfl (List.mem_cons_self ..) .nil .nil
      List.Pairwise.nil) (.throw_ (.read (.own rfl)) (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩

theorem cancel_typed : Typed [hold, failing] yields [] cancel .int [] [.fail] :=
  .let_ (live := false) rfl (.new .lit)
    (.try_ rfl
      (.let_ (live := true) rfl (.par (op := yields[0]) (da := hold) (db := failing) rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl (by simp [hold]) (by simp [failing]) (by simp [hold]) (by simp [failing]) rfl rfl
          (.cons (.move rfl rfl) (.cons .lit .nil)) .nil)
        (.add (.read (.fst (.own rfl))) (.read (.snd (.own rfl)))))
      (.atom (.read (.own rfl))))

/-- Under any schedule. -/
example : ∀ s n, match eval [hold, failing] yields n [.abort .fail 0] (Store.sched0 s) [] cancel with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [hold, failing] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok_sched cancel_fns cancel_typed

/-! Regions: an arena whose cells refer to each other, released at once. -/

/-- `region (R) { const p = R.alloc(41); const q = R.alloc(p); const pp = *q; *pp + 1 }`: a cell
holding a reference to another of the region; 42, and once the region ends, nothing left
allocated. -/
def regionEx : Expr :=
  .region "R" .int
    (.let_ "p" (.rref false 0 .int) (.ralloc "R" false .int (.lit 41))
      (.let_ "q" (.rref false 0 (.rref false 0 .int)) (.ralloc "R" false (.rref false 0 .int) (.read (var "p")))
        (.let_ "pp" (.rref false 0 .int) (.rget (var "q"))
          (.let_ "x" .int (.rget (var "pp"))
            (.add (.read (var "x")) (.lit 1))))))

example : value (eval [] [] 40 [] .empty [] regionEx) = some 42 := by
  run [regionEx]
example : freed (eval [] [] 40 [] .empty [] regionEx) := by
  run [regionEx]

theorem regionEx_typed : Typed [] [] [] regionEx .int [] [.fail] := by
  have hR : lookup "R" [("R", Slot.own (.arena 0) true)] = some (.own (.arena 0) true) := rfl
  refine .region rfl rfl ?_
  exact .let_ (live := true) rfl (.ralloc rfl (.inl rfl) rfl .lit)
    (.let_ (live := true) rfl (.ralloc rfl (.inl rfl) rfl (.readRef (.own rfl)))
      (.let_ (live := true) rfl (by simpa [Ty.shiftBy] using Typed.rget (R := "R") (k := 0) (τ := .rref false 0 .int) (.own rfl) rfl (.inl rfl) rfl)
        (.let_ (live := true) rfl (by simpa [Ty.shiftBy] using Typed.rget (R := "R") (k := 0) (τ := .int) (.own rfl) rfl (.inl rfl) rfl)
          (.add (.read (.own rfl)) .lit))))

example : ∀ n, match eval [] [] n [.abort .fail 0] .empty [] regionEx with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (by intro d hd; simp at hd) regionEx_typed

/-- `try { region (R) { const p = R.alloc(41); region (S) { const q = S.alloc(p); const pp = *q;
throw *pp + 1 } } } catch (e) { e }`: a cell of an inner region referring to one of the region around
it, and a failure that leaves both, releasing each; 42, and nothing left allocated. -/
def regionsUnwind : Expr :=
  .try_
    (.region "R" .int
      (.let_ "p" (.rref false 0 .int) (.ralloc "R" false .int (.lit 41))
        (.region "S" .int
          (.let_ "q" (.rref false 0 (.rref false 1 .int)) (.ralloc "S" false (.rref false 1 .int) (.read (var "p")))
            (.let_ "pp" (.rref false 1 .int) (.rget (var "q"))
              (.let_ "x" .int (.rget (var "pp"))
                (.let_ "y" .int (.add (.read (var "x")) (.lit 1))
                  (.throw_ (.read (var "y"))))))))))
    "e" (.atom (.read (var "e")))

example : value (eval [] [] 60 [] .empty [] regionsUnwind) = some 42 := by
  run [regionsUnwind]
example : freed (eval [] [] 60 [] .empty [] regionsUnwind) := by
  run [regionsUnwind]

theorem regionsUnwind_typed : Typed [] [] [] regionsUnwind .int [] [.fail] := by
  refine .try_ rfl (.region rfl rfl ?_) (.atom (.read (.own rfl)))
  refine .let_ (live := true) rfl (.ralloc rfl (.inl rfl) rfl .lit) (.region rfl rfl ?_)
  exact .let_ (live := true) rfl (.ralloc rfl (.inl rfl) rfl (.readRef (.own rfl)))
    (.let_ (live := true) rfl (by simpa [Ty.shiftBy] using Typed.rget (R := "S") (k := 0) (τ := .rref false 1 .int) (.own rfl) rfl (.inl rfl) rfl)
      (.let_ (live := true) rfl (by simpa [Ty.shiftBy] using Typed.rget (R := "R") (k := 1) (τ := .int) (.own rfl) rfl (.inl rfl) rfl)
        (.let_ (live := true) rfl (.add (.read (.own rfl)) .lit)
          (.throw_ (.read (.own rfl)) (by simp)))))

example : ∀ n, match eval [] [] n [.abort .fail 0] .empty [] regionsUnwind with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (by intro d hd; simp at hd) regionsUnwind_typed

/-- `region (R) { const c = Cell.new(40); const r = R.alloc(c); const d = *r; d.set(41); c.get() + 1 }`:
a `Cell` reached two ways, changed through one and read through the other; 42. -/
def cellEx : Expr :=
  .region "R" .int
    (.let_ "c" (.rref true 0 .int) (.ralloc "R" true .int (.lit 40))
      (.let_ "r" (.rref false 0 (.rref true 0 .int)) (.ralloc "R" false (.rref true 0 .int) (.read (var "c")))
        (.let_ "d" (.rref true 0 .int) (.rget (var "r"))
          (.let_ "u" .int (.rset "R" (var "d") (.lit 41))
            (.let_ "x" .int (.rget (var "c"))
              (.add (.read (var "x")) (.lit 1)))))))

example : value (eval [] [] 40 [] .empty [] cellEx) = some 42 := by
  run [cellEx]
example : freed (eval [] [] 40 [] .empty [] cellEx) := by
  run [cellEx]

theorem cellEx_typed : Typed [] [] [] cellEx .int [] [.fail] := by
  refine .region rfl rfl ?_
  exact .let_ (live := true) rfl (.ralloc rfl (.inl rfl) rfl .lit)
    (.let_ (live := true) rfl (.ralloc rfl (.inl rfl) rfl (.readRef (.own rfl)))
      (.let_ (live := true) rfl (by simpa [Ty.shiftBy] using Typed.rget (R := "R") (k := 0) (τ := .rref true 0 .int) (.own rfl) rfl (.inl rfl) rfl)
        (.let_ (live := true) rfl (.rset (.own rfl) rfl (.inl rfl) rfl .lit)
          (.let_ (live := true) rfl (by simpa [Ty.shiftBy] using Typed.rget (R := "R") (k := 0) (τ := .int) (.own rfl) rfl (.inl rfl) rfl)
            (.add (.read (.own rfl)) .lit)))))

example : ∀ n, match eval [] [] n [.abort .fail 0] .empty [] cellEx with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (by intro d hd; simp at hd) cellEx_typed

/-- Reading through a reference into the innermost region. -/
theorem Typed.rget0 (hp : PlaceTy Γ p (.rref c 0 τ) w y) (hR : lookup R Γ = some s)
    (hs : s = .own (.arena 0) true ∨ ∃ m, s = .ref m (.arena 0)) (hd : τ.rdata = true := by rfl) :
    Typed F O Γ (.rget p) τ Γ r := by
  simpa [Ty.shiftBy_zero] using Typed.rget (k := 0) hp hR hs hd

/-- `function growR<region R>(p: Ref<R, int>): Ref<R, int> uses Region<R> { R.alloc(*p + 1) }`: a
function of its caller's region, lent the arena to allocate in and read through. -/
def growR : Fn :=
  { owns := [("p", .rref false 0 .int)], refs := [("R", .mut, .arena 0)], ret := .rref false 0 .int, row := [],
    body := .let_ "x" .int (.rget (var "p"))
      (.let_ "y" .int (.add (.read (var "x")) (.lit 1)) (.ralloc "R" false .int (.read (var "y")))) }

/-- `region (R) { const p = R.alloc(41); const q = growR(p); *q }`: 42. -/
def growEx : Expr :=
  .region "R" .int
    (.let_ "p" (.rref false 0 .int) (.ralloc "R" false .int (.lit 41))
      (.let_ "q" (.rref false 0 .int) (.call 0 [.read (var "p")] [(.mut, var "R")])
        (.rget (var "q"))))

example : value (eval [growR] [] 40 [] .empty [] growEx) = some 42 := by
  run [growEx, growR]
example : freed (eval [growR] [] 40 [] .empty [] growEx) := by
  run [growEx, growR]

theorem growR_ok : FnsOk [growR] [] := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  exact ⟨by decide, _, .let_ (live := true) rfl (Typed.rget0 (R := "R") (.own rfl) rfl (.inr ⟨_, rfl⟩))
    (.let_ (live := true) rfl (.add (.read (.own rfl)) .lit) (.ralloc rfl (.inr rfl) rfl (.read (.own rfl))))⟩

theorem growEx_typed : Typed [growR] [] [] growEx .int [] [.fail] := by
  refine .region rfl rfl ?_
  refine .let_ (live := true) rfl (.ralloc rfl (.inl rfl) rfl .lit) ?_
  refine .let_ (live := true) rfl ?_ (by simpa [Ty.shiftBy] using Typed.rget (R := "R") (k := 0) (τ := .int) (.own rfl) rfl (.inl rfl) rfl)
  have := Typed.call (k := 0) (F := [growR]) (O := []) (f := 0) (d := growR) (r := [.fail])
    (Γ := [("p", .own (.rref false 0 .int) true), ("R", .own (.arena 0) true)])
    rfl rfl rfl (by simp [growR]) (.cons (.readRef (.own (x := "p") rfl)) .nil)
    (.cons (.own (x := "R") rfl) (fun _ => rfl) rfl .nil) (by simp [LentApart])
  simpa [growR, Ctx.shift] using this

example : ∀ n, match eval [growR] [] n [.abort .fail 0] .empty [] growEx with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [growR] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok growR_ok growEx_typed

/-- `region (R) { const p = R.alloc(41); region (S) { const q = growR(p); *q } }`: from inside `S`, `growR`
allocates in `R`, the region around; 42. -/
def growOuter : Expr :=
  .region "R" .int
    (.let_ "p" (.rref false 0 .int) (.ralloc "R" false .int (.lit 41))
      (.region "S" .int
        (.let_ "q" (.rref false 1 .int) (.call 0 [.read (var "p")] [(.mut, var "R")])
          (.rget (var "q")))))

example : value (eval [growR] [] 40 [] .empty [] growOuter) = some 42 := by
  run [growOuter, growR]

theorem growOuter_typed : Typed [growR] [] [] growOuter .int [] [.fail] := by
  refine .region rfl rfl ?_
  refine .let_ (live := true) rfl (.ralloc rfl (.inl rfl) rfl .lit) (.region rfl rfl ?_)
  refine .let_ (live := true) rfl ?_
    (by simpa [Ty.shiftBy] using Typed.rget (R := "R") (k := 1) (τ := .int) (.own (x := "q") rfl) rfl (.inl rfl) rfl)
  have := Typed.call (k := 1) (F := [growR]) (O := []) (f := 0) (d := growR) (r := [.fail])
    (Γ := [("S", .own (.arena 0) true), ("p", .own (.rref false 1 .int) true), ("R", .own (.arena 1) true)])
    rfl rfl rfl (by simp [growR]) (.cons (.readRef (.own (x := "p") rfl)) .nil)
    (.cons (.own (x := "R") rfl) (fun _ => rfl) rfl .nil) (by simp [LentApart])
  simpa [growR, Ctx.shift, Slot.shiftBy, Ty.shiftBy] using this

example : ∀ n, match eval [growR] [] n [.abort .fail 0] .empty [] growOuter with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [growR] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok growR_ok growOuter_typed

/-! Vectors: elements moved in, moved again as the vector grows, and dropped with it. -/

/-- `let v = []; v.push(Box.new(1)); v.push(Box.new(2)); v.len()`: 2, and nothing left allocated. -/
def vecEx : Expr :=
  .let_ "v" (.vec true (.box .int)) .vnew
    (.let_ "a" (.box .int) (.new (.lit 1))
      (.let_ "u" .int (.vpush (var "v") (.move "a"))
        (.let_ "b" (.box .int) (.new (.lit 2))
          (.let_ "w" .int (.vpush (var "v") (.move "b"))
            (.vlen (var "v"))))))

example : value (eval [] [] 40 [] .empty [] vecEx) = some 2 := by
  run [vecEx]
example : freed (eval [] [] 40 [] .empty [] vecEx) := by
  run [vecEx]

theorem vecEx_typed : Typed [] [] [] vecEx .int [] [.fail] :=
  .let_ (live := true) rfl (.vnew rfl)
    (.let_ (live := false) rfl (.new .lit)
      (.let_ (live := true) rfl (.vpush (.move rfl rfl) (.own rfl))
        (.let_ (live := false) rfl (.new .lit)
          (.let_ (live := true) rfl (.vpush (.move rfl rfl) (.own rfl))
            (.vlen (.own rfl))))))

example : ∀ n, match eval [] [] n [.abort .fail 0] .empty [] vecEx with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (by intro d hd; simp at hd) vecEx_typed

/-- `let v = []; v.push(Box.new(41)); match (v.pop()) { #None => 0, #Some(b) => *b + 1 }`: the element
taken back out of the vector, owned by the arm; 42, and nothing left allocated. -/
def vecPop : Expr :=
  .let_ "v" (.vec true (.box .int)) .vnew
    (.let_ "a" (.box .int) (.new (.lit 41))
      (.let_ "u" .int (.vpush (var "v") (.move "a"))
        (.let_ "o" (.sum .int (.box .int)) (.vpop (var "v"))
          (.case "o" "y" .int (.box .int) (.atom (.read (var "y"))) (.add (.read (deref (var "y"))) (.lit 1))))))

example : value (eval [] [] 40 [] .empty [] vecPop) = some 42 := by
  run [vecPop]
example : freed (eval [] [] 40 [] .empty [] vecPop) := by
  run [vecPop]

/-- `let v = [1, 2, 40]; { const s = v[1..3]; s.len() + s[1] }`: a slice of the vector, a vector of
its own whose cell is freed as it ends; 42, and nothing left allocated. -/
def vecSlice : Expr :=
  .let_ "v" (.vec true .int) .vnew
    (.let_ "u1" .int (.vpush (var "v") (.lit 1))
      (.let_ "u2" .int (.vpush (var "v") (.lit 2))
        (.let_ "u3" .int (.vpush (var "v") (.lit 40))
          (.let_ "lo" .int (.atom (.lit 1))
            (.let_ "hi" .int (.atom (.lit 3))
              (.let_ "k" .int (.atom (.lit 1))
                (.lendSlice "s" .ro (var "v") "lo" "hi"
                  (.let_ "n" .int (.vlen (var "s"))
                    (.lendIdx "e" .ro (var "s") "k" (.add (.read (var "e")) (.read (var "n"))))))))))))

example : value (eval [] [] 60 [] .empty [] vecSlice) = some 42 := by
  run [vecSlice]
example : freed (eval [] [] 60 [] .empty [] vecSlice) := by
  run [vecSlice]

theorem vecSlice_typed : Typed [] [] [] vecSlice .int [] [.fail] := by
  refine .let_ (live := true) rfl (.vnew rfl) ?_
  refine .let_ (live := true) rfl (.vpush .lit (.own rfl)) ?_
  refine .let_ (live := true) rfl (.vpush .lit (.own rfl)) ?_
  refine .let_ (live := true) rfl (.vpush .lit (.own rfl)) ?_
  refine .let_ (live := true) rfl (.atom .lit) ?_
  refine .let_ (live := true) rfl (.atom .lit) ?_
  refine .let_ (live := true) rfl (.atom .lit) ?_
  let Γ0 : Ctx := [("k", .own .int true), ("hi", .own .int true), ("lo", .own .int true), ("u3", .own .int true),
      ("u2", .own .int true), ("u1", .own .int true), ("v", .own (.vec true .int) true)]
  let Γs : Ctx := ("n", .own .int true) :: ("s", .ref .ro (.vec false .int)) :: freeze Γ0 ["v"]
  have hIdx : Typed [] [] Γs (.lendIdx "e" .ro (var "s") "k" (.add (.read (var "e")) (.read (var "n")))) .int Γs [.fail] := by
    have := Typed.lendIdx (F := []) (O := []) (Γ := Γs) (x := "e") (m := .ro) (y := "s") (τ := .int) (τb := .int)
      (r := [.fail]) (Γb := lendCtx .ro Γs "s") rfl (.ref rfl) (.own (x := "k") rfl) (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h) (.add (.read (.ref (x := "e") rfl)) (.read (.own (x := "n") rfl)))
    simpa [Γs, Γ0, thaw, lendCtx, freeze, Slot.ro] using this
  have h := Typed.lendSlice (F := []) (O := []) (x := "s") (m := .ro) (y := "v") (τ := .int) (r := [.fail])
    (τb := .int) (Γ := Γ0) (Γb := freeze Γ0 ["v"]) rfl (.own rfl) (.own (x := "lo") rfl) (.own (x := "hi") rfl)
    (fun h => by cases h) (.let_ (live := true) rfl (.vlen (.ref (x := "s") (m := .ro) rfl)) hIdx)
  simpa [Γ0, thaw, freeze, Slot.ro] using h

example : ∀ n, match eval [] [] n [.abort .fail 0] .empty [] vecSlice with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (by intro d hd; simp at hd) vecSlice_typed

/-- `let v = [5, 1, 2, 30]; { const s = mut v[1..3]; s[0] += 4; s[1] += 5 }; v[1] + v[3] + v[2]`: a
`mut` slice changing the elements it is of, through borrows of them, the vector out of reach
meanwhile and its own again after; 42. -/
def vecSliceMut : Expr :=
  .let_ "v" (.vec true .int) .vnew
    (.let_ "u1" .int (.vpush (var "v") (.lit 5))
      (.let_ "u2" .int (.vpush (var "v") (.lit 1))
        (.let_ "u3" .int (.vpush (var "v") (.lit 2))
          (.let_ "u4" .int (.vpush (var "v") (.lit 30))
            (.let_ "lo" .int (.atom (.lit 1))
              (.let_ "hi" .int (.atom (.lit 3))
                (.let_ "k0" .int (.atom (.lit 0))
                  (.let_ "k1" .int (.atom (.lit 1))
                    (.let_ "t" .int
                      (.lendSlice "s" .mut (var "v") "lo" "hi"
                        (.let_ "a" .int
                          (.lendIdx "e" .mut (var "s") "k0"
                            (.let_ "q" .int (.add (.read (var "e")) (.lit 4)) (.write (var "e") (.read (var "q")))))
                          (.lendIdx "f" .mut (var "s") "k1"
                            (.let_ "q" .int (.add (.read (var "f")) (.lit 5)) (.write (var "f") (.read (var "q")))))))
                      (.let_ "x" .int (.lendIdx "r" .ro (var "v") "lo" (.atom (.read (var "r"))))
                        (.let_ "z" .int (.lendIdx "r" .ro (var "v") "hi" (.atom (.read (var "r"))))
                          (.let_ "k2" .int (.atom (.lit 2))
                            (.let_ "w" .int (.lendIdx "r" .ro (var "v") "k2" (.atom (.read (var "r"))))
                              (.let_ "y" .int (.add (.read (var "x")) (.read (var "z")))
                                (.add (.read (var "y")) (.read (var "w")))))))))))))))))

example : value (eval [] [] 80 [] .empty [] vecSliceMut) = some 42 := by
  run [vecSliceMut]
example : freed (eval [] [] 80 [] .empty [] vecSliceMut) := by
  run [vecSliceMut]

theorem vecSliceMut_typed : Typed [] [] [] vecSliceMut .int [] [.fail] := by
  refine .let_ (live := true) rfl (.vnew rfl) ?_
  refine .let_ (live := true) rfl (.vpush .lit (.own rfl)) ?_
  refine .let_ (live := true) rfl (.vpush .lit (.own rfl)) ?_
  refine .let_ (live := true) rfl (.vpush .lit (.own rfl)) ?_
  refine .let_ (live := true) rfl (.vpush .lit (.own rfl)) ?_
  refine .let_ (live := true) rfl (.atom .lit) ?_
  refine .let_ (live := true) rfl (.atom .lit) ?_
  refine .let_ (live := true) rfl (.atom .lit) ?_
  refine .let_ (live := true) rfl (.atom .lit) ?_
  let Γ0 : Ctx := [("k1", .own .int true), ("k0", .own .int true), ("hi", .own .int true), ("lo", .own .int true),
    ("u4", .own .int true), ("u3", .own .int true), ("u2", .own .int true), ("u1", .own .int true),
    ("v", .own (.vec true .int) true)]
  let Γs : Ctx := ("s", .ref .mut (.vec false .int)) :: hide Γ0 "v"
  -- `{ const e = mut s[k]; *e = *e + d }`, in the slice's scope.
  have bump : ∀ (Γ : Ctx) (e k : Var) (d : Int), lookup e Γ = none → lookup k Γ = some (.own .int true) →
      lookup "s" Γ = some (.ref .mut (.vec false .int)) → e ≠ "q" → lookup "q" (lendCtx .mut Γ "s") = none →
      Typed [] [] Γ (.lendIdx e .mut (var "s") k
        (.let_ "q" .int (.add (.read (var e)) (.lit d)) (.write (var e) (.read (var "q"))))) .int
        (thaw Γ ["s"] (lendCtx .mut Γ "s")) [.fail] := by
    intro Γ e k d he hk hs heq hq
    have hq' : lookup "q" ((e, .ref .mut .int) :: lendCtx .mut Γ "s") = none := by
      simp only [lookup]; rw [if_neg (Ne.symm heq)]; exact hq
    have he' : lookup e (("q", .own .int true) :: (e, .ref .mut .int) :: lendCtx .mut Γ "s") = some (.ref .mut .int) := by
      simp only [lookup]; rw [if_neg heq]; simp
    exact Typed.lendIdx (F := []) (O := []) (Γ := Γ) (x := e) (m := .mut) (y := "s") (z := k) (τ := .int)
      (τb := .int) (r := [.fail]) (Γb := lendCtx .mut Γ "s") he (.ref hs) (.own hk) (fun _ => rfl) (fun _ => rfl)
      (fun _ _ _ _ h => by rw [hs] at h; cases h)
      (.let_ (live := true) hq' (.add (.read (.ref (x := e) (m := .mut) (by simp [lookup]))) .lit)
        (.write (.read (.own (x := "q") (by simp [lookup]))) (.ref (x := e) (m := .mut) he')))
  have hbody : Typed [] [] ((("s", .ref .mut (.vec false .int)) :: lendCtx .mut Γ0 "v"))
      (.let_ "a" .int
        (.lendIdx "e" .mut (var "s") "k0"
          (.let_ "q" .int (.add (.read (var "e")) (.lit 4)) (.write (var "e") (.read (var "q")))))
        (.lendIdx "f" .mut (var "s") "k1"
          (.let_ "q" .int (.add (.read (var "f")) (.lit 5)) (.write (var "f") (.read (var "q"))))))
      .int (("s", .ref .mut (.vec false .int)) :: hide Γ0 "v") [.fail] := by
    have h1 := bump (("s", .ref .mut (.vec false .int)) :: lendCtx .mut Γ0 "v") "e" "k0" 4
      (by simp [Γ0, lendCtx, hide, lookup]) (by simp [Γ0, lendCtx, hide, lookup, Slot.ty])
      (by simp [lookup]) (by decide) (by simp [Γ0, lendCtx, hide, lookup])
    have h2 := bump (("a", .own .int true) :: ("s", .ref .mut (.vec false .int)) :: lendCtx .mut Γ0 "v") "f" "k1" 5
      (by simp [Γ0, lendCtx, hide, lookup]) (by simp [Γ0, lendCtx, hide, lookup, Slot.ty])
      (by simp [lookup]) (by decide) (by simp [Γ0, lendCtx, hide, lookup])
    refine .let_ (live := true) (by simp [Γ0, lendCtx, hide, lookup]) (by simpa [Γ0, lendCtx, hide, thaw, Slot.ty,
      Slot.shell, Ty.shell] using h1) ?_
    simpa [Γ0, lendCtx, hide, thaw, Slot.ty, Slot.shell, Ty.shell] using h2
  have h := Typed.lendSlice (F := []) (O := []) (x := "s") (m := .mut) (y := "v") (τ := .int) (r := [.fail])
    (τb := .int) (Γ := Γ0) (Γb := hide Γ0 "v") rfl (.own rfl) (.own (x := "lo") rfl) (.own (x := "hi") rfl)
    (fun _ => rfl) hbody
  refine .let_ (live := true) rfl (by simpa [Γ0, thaw, hide, Slot.ty, Slot.shell] using h) ?_
  refine .let_ (live := true) rfl (.lendIdx rfl (.own rfl) (.own rfl) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h) (.atom (.read (.ref rfl)))) ?_
  refine .let_ (live := true) rfl (.lendIdx rfl (.own rfl) (.own rfl) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h) (.atom (.read (.ref rfl)))) ?_
  refine .let_ (live := true) rfl (.atom .lit) ?_
  refine .let_ (live := true) rfl (.lendIdx rfl (.own rfl) (.own rfl) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h) (.atom (.read (.ref rfl)))) ?_
  exact .let_ (live := true) rfl (.add (.read (.own rfl)) (.read (.own rfl))) (.add (.read (.own rfl)) (.read (.own rfl)))

example : ∀ n, match eval [] [] n [.abort .fail 0] .empty [] vecSliceMut with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (by intro d hd; simp at hd) vecSliceMut_typed

/-- A slice does not grow: pushing to one is rejected, for it would move the elements it shares with
its vector. -/
theorem slice_push_rejected : ¬ Typed F O [("s", .ref .mut (.vec false .int))] (.vpush (var "s") (.lit 1)) τ Γ' r := by
  have key : ∀ w y, ¬ PlaceTy [("s", .ref .mut (.vec false .int))] (var "s") (.vec true .int) w y := by
    intro w y hp
    cases hp with
    | own h => simp [lookup] at h
    | ref h => simp [lookup] at h
    | half h => simp [lookup] at h
  intro h
  cases h with
  | vpush ha hp =>
    cases ha
    exact key _ _ hp

/-- `let v = []; v.push(1); v.push(41); const i = 1; { const e = mut v[i]; *e = *e + 1 }; v[i]`:
an element changed and read through borrows of it; 42. -/
def vecIdx : Expr :=
  .let_ "v" (.vec true .int) .vnew
    (.let_ "u" .int (.vpush (var "v") (.lit 1))
      (.let_ "w" .int (.vpush (var "v") (.lit 41))
        (.let_ "i" .int (.atom (.lit 1))
          (.let_ "t" .int
            (.lendIdx "e" .mut (var "v") "i"
              (.let_ "s" .int (.add (.read (var "e")) (.lit 1)) (.write (var "e") (.read (var "s")))))
            (.lendIdx "r" .ro (var "v") "i" (.atom (.read (var "r"))))))))

example : value (eval [] [] 40 [] .empty [] vecIdx) = some 42 := by
  run [vecIdx]
example : freed (eval [] [] 40 [] .empty [] vecIdx) := by
  run [vecIdx]

theorem vecIdx_typed : Typed [] [] [] vecIdx .int [] [.fail] :=
  .let_ (live := true) rfl (.vnew rfl)
    (.let_ (live := true) rfl (.vpush .lit (.own rfl))
      (.let_ (live := true) rfl (.vpush .lit (.own rfl))
        (.let_ (live := true) rfl (.atom .lit)
          (.let_ (live := true) rfl
            (.lendIdx rfl (.own rfl) (.own rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ _ _ h => by simp [lookup] at h)
              (.let_ (live := true) rfl (.add (.read (.ref rfl)) .lit) (.write (.read (.own rfl)) (.ref (m := .mut) rfl))))
            (.lendIdx rfl (.own rfl) (.own rfl) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
              (.atom (.read (.ref rfl))))))))

example : ∀ n, match eval [] [] n [.abort .fail 0] .empty [] vecIdx with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (by intro d hd; simp at hd) vecIdx_typed

/-- `let v = []; v.push(1); const i = 5; v[i]`: out of bounds, a panic. -/
def vecOob : Expr :=
  .let_ "v" (.vec true .int) .vnew
    (.let_ "u" .int (.vpush (var "v") (.lit 1))
      (.let_ "i" .int (.atom (.lit 5))
        (.lendIdx "r" .ro (var "v") "i" (.atom (.read (var "r"))))))

example : (eval [] [] 40 [] .empty [] vecOob).1 = .panic := by
  run [vecOob]

/-- Pushing to a vector while one of its elements is borrowed `mut`: the vector is out of reach
while the borrow lives, so the push, which would move the element, does not check. -/
theorem pushWhileBorrowed_rejected :
    ¬ Typed [] [] [("i", .own .int true), ("v", .own (.vec true .int) true)]
      (.lendIdx "e" .mut (var "v") "i" (.vpush (var "v") (.lit 1))) τ Γ' r := by
  have key : ∀ {τe τ w y}, PlaceTy (("e", .ref .mut τe) ::
      lendCtx .mut [("i", .own .int true), ("v", .own (.vec true .int) true)] "v") (var "v") τ w y → False := by
    intro τe τ w y hp
    cases hp <;> simp_all [lookup, lendCtx, hide]
  intro h
  cases h with
  | lendIdx _ hpv _ _ _ _ hb =>
    cases hpv with
    | own hv =>
      cases hb with
      | vpush ha hp =>
        cases ha
        exact key hp
    | ref hv => simp [lookup] at hv
    | half hv => simp [lookup] at hv

/-! Generators: a producer yields as its consumer asks, each waiting in the generator's frame while
the other runs. -/

/-- `Next`, asking a generator for its next value, and `Yield`, giving one. -/
def nextOp : Op := { owns := [], refs := [], ret := .sum .int .int }
def yieldOp : Op := { owns := [.int], refs := [], ret := .int }
def genOps : List Op := [nextOp, yieldOp]

/-- `function* three() { yield 10; yield 20; yield 12; }` -/
def three : Fn :=
  { owns := [], refs := [], ret := .int, row := [.eff 1],
    body := .let_ "u" .int (.perform 1 [.lit 10] [])
      (.let_ "v" .int (.perform 1 [.lit 20] []) (.let_ "w" .int (.perform 1 [.lit 12] []) (.atom (.lit 0)))) }

/-- What `g.next()` gives, or 0 once the generator is done, into `x`. -/
def nextOr0 (x : Var) (rest : Expr) : Expr :=
  .let_ x .int (.let_ "a" (.sum .int .int) (.perform 0 [] [])
    (.case "a" "y" .int .int (.atom (.read (var "y"))) (.atom (.read (var "y"))))) rest

/-- `const g = three(); g.next() + g.next() + g.next() + (g.next() ?? 0)`: 42, the fourth asking
answered `#Done`. -/
def genSum : Expr :=
  .gen 0 1 .int .int 0 [] []
    (nextOr0 "x1" (nextOr0 "x2" (nextOr0 "x3" (nextOr0 "x4"
      (.let_ "s" .int (.add (.read (var "x1")) (.read (var "x2")))
        (.let_ "t" .int (.add (.read (var "s")) (.read (var "x3")))
          (.add (.read (var "t")) (.read (var "x4")))))))))

example : value (eval [three] genOps 60 [.abort .fail 0] .empty [] genSum) = some 42 := by
  run [genSum, three, nextOr0, genOps, nextOp, yieldOp]
example : freed (eval [three] genOps 60 [.abort .fail 0] .empty [] genSum) := by
  run [genSum, three, nextOr0, genOps, nextOp, yieldOp]

/-- `const x = g.next() ?? 0; rest`, typed. -/
theorem nextOr0_typed (hx : x ∉ Γ.map Prod.fst) (ha : "a" ∉ Γ.map Prod.fst) (hy : "y" ∉ Γ.map Prod.fst)
    (hr : Label.eff 0 ∈ r)
    (hrest : Typed F genOps ((x, .own .int true) :: Γ) rest τ ((x, .own .int live) :: Γ') r) :
    Typed F genOps Γ (nextOr0 x rest) τ Γ' r := by
  refine .let_ (lookup_none_of_keys hx) ?_ hrest
  refine .let_ (live := false) (lookup_none_of_keys ha)
    (Typed.perform (op := nextOp) rfl hr .nil .nil .nil) ?_
  have hset : setSlot (("a", Slot.own (.sum .int .int) true) :: Γ) "a" (.own (.sum .int .int) false) =
      ("a", .own (.sum .int .int) false) :: Γ := setSlot_head Γ ha
  refine .case (Γ₁ := ("a", .own (.sum .int .int) false) :: Γ) (Γ₂ := ("a", .own (.sum .int .int) false) :: Γ)
    (l₁ := true) (l₂ := true) (by simp [lookup]) rfl
    (by simp only [lookup]; rw [if_neg (by decide)]; exact lookup_none_of_keys hy) ?_ ?_ (Weaker.refl _) (Weaker.refl _)
  · rw [hset]; exact .atom (.read (.own rfl))
  · rw [hset]; exact .atom (.read (.own rfl))

theorem three_ok : FnsOk [three] genOps := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  refine ⟨by decide, ?_⟩
  simp only [three, FnOk]
  exact ⟨_, .let_ (live := true) rfl (.perform (op := yieldOp) rfl (List.mem_singleton_self _) (.cons .lit .nil) .nil .nil)
    (.let_ (live := true) rfl (.perform (op := yieldOp) rfl (List.mem_singleton_self _) (.cons .lit .nil) .nil .nil)
      (.let_ (live := true) rfl (.perform (op := yieldOp) rfl (List.mem_singleton_self _) (.cons .lit .nil) .nil .nil)
        (.atom .lit)))⟩

theorem genSum_typed : Typed [three] genOps [] genSum .int [] [.fail] := by
  refine .gen (Γ₁ := []) (ys := []) (Γb := []) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by simp [three]) (by simp [three]) (by simp [three]) .nil .nil List.Pairwise.nil ?_ rfl
  simp only [roots, List.filter_nil, List.map_nil, hideAll, freeze]
  refine nextOr0_typed (live := true) (by simp) (by simp) (by simp) (by simp) ?_
  refine nextOr0_typed (live := true) (by simp) (by simp) (by simp) (by simp) ?_
  refine nextOr0_typed (live := true) (by simp) (by simp) (by simp) (by simp) ?_
  refine nextOr0_typed (live := true) (by simp) (by simp) (by simp) (by simp) ?_
  exact .let_ (live := true) rfl (.add (.read (.own rfl)) (.read (.own rfl)))
    (.let_ (live := true) rfl (.add (.read (.own rfl)) (.read (.own rfl))) (.add (.read (.own rfl)) (.read (.own rfl))))

example : ∀ n, match eval [three] genOps n [.abort .fail 0] .empty [] genSum with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [three] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok three_ok genSum_typed

/-- `function* boxed() { const b = Box.new(5); yield *b; yield 7; }` -/
def boxed : Fn :=
  { owns := [], refs := [], ret := .int, row := [.eff 1],
    body := .let_ "b" (.box .int) (.new (.lit 5))
      (.let_ "u" .int (.perform 1 [.read (deref (var "b"))] []) (.let_ "v" .int (.perform 1 [.lit 7] []) (.atom (.lit 0)))) }

/-- `const g = boxed(); g.next() ?? 0`: the consumer asks once and ends, and the producer, still owning
its box, is dropped where it waits; 5, and nothing left allocated. -/
def genEarly : Expr := .gen 0 1 .int .int 0 [] [] (nextOr0 "x" (.atom (.read (var "x"))))

example : value (eval [boxed] genOps 40 [.abort .fail 0] .empty [] genEarly) = some 5 := by
  run [genEarly, boxed, nextOr0, genOps, nextOp, yieldOp]
example : freed (eval [boxed] genOps 40 [.abort .fail 0] .empty [] genEarly) := by
  run [genEarly, boxed, nextOr0, genOps, nextOp, yieldOp]

theorem boxed_ok : FnsOk [boxed] genOps := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  refine ⟨by decide, ?_⟩
  simp only [boxed, FnOk]
  exact ⟨_, .let_ (live := true) rfl (.new .lit)
    (.let_ (live := true) rfl (.perform (op := yieldOp) rfl (List.mem_singleton_self _)
        (.cons (.read (.deref (.own rfl))) .nil) .nil .nil)
      (.let_ (live := true) rfl (.perform (op := yieldOp) rfl (List.mem_singleton_self _) (.cons .lit .nil) .nil .nil)
        (.atom .lit)))⟩

theorem genEarly_typed : Typed [boxed] genOps [] genEarly .int [] [.fail] := by
  refine .gen (Γ₁ := []) (ys := []) (Γb := []) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by simp [boxed]) (by simp [boxed]) (by simp [boxed]) .nil .nil List.Pairwise.nil ?_ rfl
  simp only [roots, List.filter_nil, List.map_nil, hideAll, freeze]
  exact nextOr0_typed (live := true) (by simp) (by simp) (by simp) (by simp) (.atom (.read (.own rfl)))

example : ∀ n, match eval [boxed] genOps n [.abort .fail 0] .empty [] genEarly with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [boxed] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok boxed_ok genEarly_typed

/-- `function* fails() { yield 1; throw 41; }` -/
def fails : Fn :=
  { owns := [], refs := [], ret := .int, row := [.eff 1, .fail],
    body := .let_ "u" .int (.perform 1 [.lit 1] []) (.throw_ (.lit 41)) }

/-- `try { const g = fails(); const b = Box.new(1); g.next() ?? 0; g.next() ?? 0 } catch (e) { e + 1 }`:
the producer fails as the consumer waits, owning a box, which is dropped where it waits; 42, and
nothing left allocated. -/
def genFails : Expr :=
  .try_ (.gen 0 1 .int .int 0 [] []
      (.let_ "b" (.box .int) (.new (.lit 1)) (nextOr0 "x" (nextOr0 "z" (.atom (.read (var "z")))))))
    "e" (.add (.read (var "e")) (.lit 1))

example : value (eval [fails] genOps 60 [.abort .fail 0] .empty [] genFails) = some 42 := by
  run [genFails, fails, nextOr0, genOps, nextOp, yieldOp]
example : freed (eval [fails] genOps 60 [.abort .fail 0] .empty [] genFails) := by
  run [genFails, fails, nextOr0, genOps, nextOp, yieldOp]

/-- What `v.pop()` gives, or 0 once `v` is empty, into `x`. -/
def popOr0 (x : Var) (rest : Expr) : Expr :=
  .let_ x .int (.let_ "a" (.sum .int .int) (.vpop (var "v"))
    (.case "a" "y" .int .int (.atom (.read (var "y"))) (.atom (.read (var "y"))))) rest

/-- `function* drain(v: mut Vec<int>) { yield v.pop() ?? 0; yield v.pop() ?? 0; }`: a producer
lent a vector it changes. -/
def drain : Fn :=
  { owns := [], refs := [("v", .mut, .vec true .int)], ret := .int, row := [.eff 1],
    body := popOr0 "x" (.let_ "u" .int (.perform 1 [.read (var "x")] [])
      (popOr0 "z" (.let_ "w" .int (.perform 1 [.read (var "z")] []) (.atom (.lit 0))))) }

/-- `let v = [1, 1, 40]; const s = { const g = drain(mut v); (g.next() ?? 0) + (g.next() ?? 0) };
s + v.len()`: the producer takes two elements out of the vector lent it, which is out of the
consumer's reach meanwhile, and the vector, one element left, is the code around's again; 42. -/
def genDrain : Expr :=
  .let_ "v" (.vec true .int) .vnew
    (.let_ "u1" .int (.vpush (var "v") (.lit 1))
      (.let_ "u2" .int (.vpush (var "v") (.lit 1))
        (.let_ "u3" .int (.vpush (var "v") (.lit 40))
          (.let_ "s" .int (.gen 0 1 .int .int 0 [] [⟨"v", .mut, .vec true .int, .var "v"⟩]
              (nextOr0 "x1" (nextOr0 "x2" (.add (.read (var "x1")) (.read (var "x2"))))))
            (.let_ "n" .int (.vlen (var "v")) (.add (.read (var "s")) (.read (var "n"))))))))

example : value (eval [drain] genOps 80 [.abort .fail 0] .empty [] genDrain) = some 42 := by
  run [genDrain, drain, popOr0, nextOr0, genOps, nextOp, yieldOp]
example : freed (eval [drain] genOps 80 [.abort .fail 0] .empty [] genDrain) := by
  run [genDrain, drain, popOr0, nextOr0, genOps, nextOp, yieldOp]

/-- `const x = v.pop() ?? 0; rest`, typed. -/
theorem popOr0_typed (hv : lookup "v" Γ = some (.ref .mut (.vec true .int))) (hx : x ∉ Γ.map Prod.fst)
    (ha : "a" ∉ Γ.map Prod.fst) (hy : "y" ∉ Γ.map Prod.fst)
    (hrest : Typed F O ((x, .own .int true) :: Γ) rest τ ((x, .own .int live) :: Γ') r) :
    Typed F O Γ (popOr0 x rest) τ Γ' r := by
  refine .let_ (lookup_none_of_keys hx) ?_ hrest
  refine .let_ (live := false) (lookup_none_of_keys ha) (.vpop (.ref hv) rfl) ?_
  have hset : setSlot (("a", Slot.own (.sum .int .int) true) :: Γ) "a" (.own (.sum .int .int) false) =
      ("a", .own (.sum .int .int) false) :: Γ := setSlot_head Γ ha
  refine .case (Γ₁ := ("a", .own (.sum .int .int) false) :: Γ) (Γ₂ := ("a", .own (.sum .int .int) false) :: Γ)
    (l₁ := true) (l₂ := true) (by simp [lookup]) rfl
    (by simp only [lookup]; rw [if_neg (by decide)]; exact lookup_none_of_keys hy) ?_ ?_ (Weaker.refl _) (Weaker.refl _)
  · rw [hset]; exact .atom (.read (.own rfl))
  · rw [hset]; exact .atom (.read (.own rfl))

theorem drain_ok : FnsOk [drain] genOps := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  refine ⟨by decide, ?_⟩
  simp only [drain, FnOk]
  refine ⟨[("v", .ref .mut (.vec true .int))], popOr0_typed (live := true) rfl (by decide) (by decide) (by decide) ?_⟩
  refine .let_ (live := true) rfl (.perform (op := yieldOp) rfl (List.mem_singleton_self _)
    (.cons (.read (.own rfl)) .nil) .nil .nil) ?_
  refine popOr0_typed (live := true) rfl (by decide) (by decide) (by decide) ?_
  exact .let_ (live := true) rfl (.perform (op := yieldOp) rfl (List.mem_singleton_self _)
    (.cons (.read (.own rfl)) .nil) .nil .nil) (.atom .lit)

theorem genDrain_typed : Typed [drain] genOps [] genDrain .int [] [.fail] := by
  refine .let_ (live := true) rfl (.vnew rfl) ?_
  refine .let_ (live := true) rfl (.vpush .lit (.own rfl)) ?_
  refine .let_ (live := true) rfl (.vpush .lit (.own rfl)) ?_
  refine .let_ (live := true) rfl (.vpush .lit (.own rfl)) ?_
  let Γ0 : Ctx := [("u3", .own .int true), ("u2", .own .int true), ("u1", .own .int true), ("v", .own (.vec true .int) true)]
  have hg : Typed [drain] genOps Γ0 (.gen 0 1 .int .int 0 [] [⟨"v", .mut, .vec true .int, .var "v"⟩]
      (nextOr0 "x1" (nextOr0 "x2" (.add (.read (var "x1")) (.read (var "x2")))))) .int Γ0 [.fail] := by
    have hb : Typed [drain] genOps (freeze (hideAll Γ0 (roots .mut [(.mut, "v")])) (roots .ro [(.mut, "v")]))
        (nextOr0 "x1" (nextOr0 "x2" (.add (.read (var "x1")) (.read (var "x2"))))) .int (hide Γ0 "v")
        (.eff 0 :: [.fail]) := by
      simp only [roots, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, hideAll, freeze]
      refine nextOr0_typed (live := true) (by simp [Γ0, hide, hideAll]) (by simp [Γ0, hide, hideAll]) (by simp [Γ0, hide, hideAll]) (by simp) ?_
      refine nextOr0_typed (live := true) (by simp [Γ0, hide, hideAll]) (by simp [Γ0, hide, hideAll]) (by simp [Γ0, hide, hideAll]) (by simp) ?_
      exact .add (.read (.own rfl)) (.read (.own rfl))
    have h := Typed.gen (F := [drain]) (O := genOps) (Γ := Γ0) (Γ₁ := Γ0) (ys := [(.mut, "v")]) (r := [.fail])
      (eN := 0) (eY := 1) (τy := .int) (τb := .int) (f := 0) (d := drain) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl (by simp [drain]) (by simp [drain]) rfl .nil (.mut (.own rfl) rfl rfl .nil) (by simp [Exclusive]) hb rfl
    simpa [Γ0, roots, hideAll, unhideAll, hide, thaw, freeze] using h
  refine .let_ (live := true) rfl hg ?_
  exact .let_ (live := true) rfl (.vlen (.own rfl)) (.add (.read (.own rfl)) (.read (.own rfl)))

example : ∀ n, match eval [drain] genOps n [.abort .fail 0] .empty [] genDrain with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [drain] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok drain_ok genDrain_typed

/-! Scopes: a body starts tasks as it runs, each a closure called once that moved in what it
captured; the body and its tasks give way to each other, in any order a schedule picks. -/

/-- `Yield`, by which a scope's body and tasks give way, and `Spawn`, by which they start a task. -/
def scYield : Op := { owns := [], refs := [], ret := .int }
def scSpawn : Op := { owns := [.fn .once .int .int [.eff 0]], refs := [], ret := .int }
def scOps : List Op := [scYield, scSpawn]

/-- `(_) => { yield; *b }`, a closure that captured a box `b`. -/
def tk : Fn :=
  { owns := [("p", .int)], refs := [], ret := .int, row := [.eff 0], cap := some ("b", .box .int, .once),
    body := .let_ "u" .int (.perform 0 [] []) (.atom (.read (deref (var "b")))) }

/-- `scope((s) => { const b = Box.new(5); s.spawn(() => …b…); const c = Box.new(7);
s.spawn(() => …c…); yield; 42 })`: two tasks started as the body runs, each owning a box; 42, and
nothing left allocated, whichever way they interleave. -/
def scopeEx : Expr :=
  .scope 0 1 .int
    (.let_ "b" (.box .int) (.new (.lit 5))
      (.let_ "k" (.fn .once .int .int [.eff 0]) (.lam 0 (.move "b"))
        (.let_ "u" .int (.perform 1 [.move "k"] [])
          (.let_ "c" (.box .int) (.new (.lit 7))
            (.let_ "k2" (.fn .once .int .int [.eff 0]) (.lam 0 (.move "c"))
              (.let_ "u2" .int (.perform 1 [.move "k2"] [])
                (.let_ "y" .int (.perform 0 [] []) (.atom (.lit 42)))))))))

example : value (eval [tk] scOps 80 [] .empty [] scopeEx) = some 42 := by
  run [scopeEx, tk, scOps, scYield, scSpawn, mkTask, cloFn]
example : freed (eval [tk] scOps 80 [] .empty [] scopeEx) := by
  run [scopeEx, tk, scOps, scYield, scSpawn, mkTask, cloFn]
example : value (eval [tk] scOps 80 [] (Store.sched0 fun _ => false) [] scopeEx) = some 42 := by
  run [scopeEx, tk, scOps, scYield, scSpawn, mkTask, cloFn]
example : freed (eval [tk] scOps 80 [] (Store.sched0 fun _ => false) [] scopeEx) := by
  run [scopeEx, tk, scOps, scYield, scSpawn, mkTask, cloFn]

theorem tk_ok : FnsOk [tk] scOps := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  refine ⟨by decide, ?_⟩
  simp only [tk, FnOk, fnCtx, cloFn, ownCtx, refCtx]
  exact ⟨by decide, [("p", .own .int true), ("b", .own (.box .int) true)], .let_ (live := true) rfl (.perform (op := scYield) rfl (List.mem_singleton_self _) .nil .nil .nil)
    (.atom (.read (.deref (.own rfl))))⟩

theorem scopeEx_typed : Typed [tk] scOps [] scopeEx .int [] [.fail] := by
  refine .scope (op := scYield) (opS := scSpawn) (rT := [.eff 0]) rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
    (by simp) (by simp) rfl ?_
  refine .let_ (live := false) rfl (.new .lit) ?_
  refine .let_ (live := false) rfl (.lam (d := tk) rfl rfl rfl rfl rfl (.move rfl rfl) rfl) ?_
  refine .let_ (live := true) rfl (.perform (op := scSpawn) rfl (by simp) (.cons (.move rfl rfl) .nil) .nil .nil) ?_
  refine .let_ (live := false) rfl (.new .lit) ?_
  refine .let_ (live := false) rfl (.lam (d := tk) rfl rfl rfl rfl rfl (.move rfl rfl) rfl) ?_
  refine .let_ (live := true) rfl (.perform (op := scSpawn) rfl (by simp) (.cons (.move rfl rfl) .nil) .nil .nil) ?_
  exact .let_ (live := true) rfl (.perform (op := scYield) rfl (by simp) .nil .nil .nil) (.atom .lit)

/-- Under any schedule. -/
example (s : Nat → Bool) : ∀ n, match eval [tk] scOps n [.abort .fail 0] (Store.sched0 s) [] scopeEx with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [tk] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok_sched tk_ok scopeEx_typed s

/-- `(_) => { yield; throw 41 }` and `(_) => { yield; *b }`, closures that captured a box each. -/
def badTk : Fn :=
  { owns := [("p", .int)], refs := [], ret := .int, row := [.eff 0, .fail], cap := some ("b", .box .int, .once),
    body := .let_ "u" .int (.perform 0 [] []) (.throw_ (.lit 41)) }
def okTk : Fn :=
  { owns := [("p", .int)], refs := [], ret := .int, row := [.eff 0, .fail], cap := some ("b", .box .int, .once),
    body := .let_ "u" .int (.perform 0 [] []) (.atom (.read (deref (var "b")))) }
def scSpawnF : Op := { owns := [.fn .once .int .int [.eff 0, .fail]], refs := [], ret := .int }

/-- `try { scope((s) => { s.spawn(bad); s.spawn(ok); const d = Box.new(1); yield; yield; 0 }) }
catch (e) { e + 1 }`: a task fails; what is left of the scope, its body and the other task, each
owning a box, is dropped where it waits; 42, and nothing left allocated, whichever way they
interleave. -/
def scopeFail : Expr :=
  .try_ (.scope 0 1 .int
    (.let_ "b" (.box .int) (.new (.lit 5))
      (.let_ "k" (.fn .once .int .int [.eff 0, .fail]) (.lam 0 (.move "b"))
        (.let_ "u" .int (.perform 1 [.move "k"] [])
          (.let_ "c" (.box .int) (.new (.lit 7))
            (.let_ "k2" (.fn .once .int .int [.eff 0, .fail]) (.lam 1 (.move "c"))
              (.let_ "u2" .int (.perform 1 [.move "k2"] [])
                (.let_ "d" (.box .int) (.new (.lit 1))
                  (.let_ "y" .int (.perform 0 [] []) (.let_ "y2" .int (.perform 0 [] []) (.atom (.lit 0))))))))))))
    "e" (.add (.read (var "e")) (.lit 1))

example : value (eval [badTk, okTk] [scYield, scSpawnF] 120 [.abort .fail 0] .empty [] scopeFail) = some 42 := by
  run [scopeFail, badTk, okTk, scYield, scSpawnF, mkTask, cloFn]
example : freed (eval [badTk, okTk] [scYield, scSpawnF] 120 [.abort .fail 0] .empty [] scopeFail) := by
  run [scopeFail, badTk, okTk, scYield, scSpawnF, mkTask, cloFn]
example : value (eval [badTk, okTk] [scYield, scSpawnF] 120 [.abort .fail 0] (Store.sched0 fun _ => false) []
    scopeFail) = some 42 := by
  run [scopeFail, badTk, okTk, scYield, scSpawnF, mkTask, cloFn]
example : freed (eval [badTk, okTk] [scYield, scSpawnF] 120 [.abort .fail 0] (Store.sched0 fun _ => false) []
    scopeFail) := by
  run [scopeFail, badTk, okTk, scYield, scSpawnF, mkTask, cloFn]

/-- `region (R) { const l = RegionList.new(); l.push(40); l.push(2); l[0] + l[1] }`: a list of the
region, its elements cells of the region, all released as it ends; 42. -/
def regionList : Expr :=
  .region "R" .int
    (.let_ "l" (.rref false 0 (.vec true .int)) (.rlnew "R" .int)
      (.let_ "u" .int (.rpush "R" .int (var "l") (.lit 40))
        (.let_ "v" .int (.rpush "R" .int (var "l") (.lit 2))
          (.let_ "i" .int (.atom (.lit 0))
            (.let_ "j" .int (.atom (.lit 1))
              (.let_ "x" .int (.rnth "R" (var "l") "i")
                (.let_ "y" .int (.rnth "R" (var "l") "j")
                  (.add (.read (var "x")) (.read (var "y"))))))))))

example : value (eval [] [] 40 [] .empty [] regionList) = some 42 := by
  run [regionList]
example : freed (eval [] [] 40 [] .empty [] regionList) := by
  run [regionList]

theorem regionList_typed : Typed [] [] [] regionList .int [] [.fail] := by
  refine .region rfl rfl ?_
  refine .let_ (live := true) rfl (.rlnew (k := 0) rfl (.inl rfl) rfl) ?_
  refine .let_ (live := true) rfl (.rpush (k := 0) (.own rfl) rfl (.inl rfl) rfl .lit) ?_
  refine .let_ (live := true) rfl (.rpush (k := 0) (.own rfl) rfl (.inl rfl) rfl .lit) ?_
  refine .let_ (live := true) rfl (.atom .lit) ?_
  refine .let_ (live := true) rfl (.atom .lit) ?_
  have hx := Typed.rnth (F := []) (O := []) (r := [.fail]) (k := 0) (τ := .int) (R := "R") (c := false) (z := "i")
    (Γ := [("j", .own .int true), ("i", .own .int true), ("v", .own .int true), ("u", .own .int true),
      ("l", .own (.rref false 0 (.vec true .int)) true), ("R", .own (.arena 0) true)]) (.own (x := "l") rfl) (.own rfl) rfl (.inl rfl) rfl
  refine .let_ (live := true) rfl (by simpa [Ctx.shift] using hx) ?_
  have hy := Typed.rnth (F := []) (O := []) (r := [.fail]) (k := 0) (τ := .int) (R := "R") (c := false) (z := "j")
    (Γ := [("x", .own .int true), ("j", .own .int true), ("i", .own .int true), ("v", .own .int true),
      ("u", .own .int true), ("l", .own (.rref false 0 (.vec true .int)) true), ("R", .own (.arena 0) true)])
    (.own (x := "l") rfl) (.own rfl) rfl (.inl rfl) rfl
  refine .let_ (live := true) rfl (by simpa [Ctx.shift] using hy) ?_
  exact .add (.read (.own rfl)) (.read (.own rfl))

example : ∀ n, match eval [] [] n [.abort .fail 0] .empty [] regionList with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [] [] σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (by intro d hd; simp at hd) regionList_typed

theorem ralloc_ty (h : Typed F O Γ (.ralloc R c τ a) t Γ' r) :
    ∃ k s, t = .rref c k τ ∧ lookup R Γ = some s ∧ (s = .own (.arena k) true ∨ s = .ref .mut (.arena k)) := by
  cases h; exact ⟨_, _, rfl, ‹_›, ‹_›⟩

/-- `region (R) { R.alloc(1) }`: a reference into the region cannot be its value — no type said of the
code around refers to the region. -/
theorem escape_rejected : ¬ Typed [] [] [] (.region "R" τ (.ralloc "R" false .int (.lit 1))) τ Γ' r := by
  intro h
  cases h with
  | region _ _ hb =>
    obtain ⟨k, s, ht, hl, hs⟩ := ralloc_ty hb
    simp only [lookup, ↓reduceIte, Option.some.injEq] at hl
    subst hl
    rcases hs with hs | hs <;> simp only [Slot.own.injEq, Ty.arena.injEq, reduceCtorEq] at hs
    obtain ⟨rfl, -⟩ := hs
    cases τ <;> simp [Ty.shiftBy] at ht

end FlyCore.Ownership.Examples
