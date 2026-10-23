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
    body := .let_ "t" .int (.add (.read (deref (var "r"))) (.read (deref (var "b"))))
      (.let_ "u" .int (.write (deref (var "r")) (.read (var "t"))) (.atom (.read (deref (var "r"))))) }

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
    body := .let_ "t" (.box .int) (.new (.lit 7))
      (.let_ "u" .int (.assign (var "a") (.box .int) (.move "t")) (.atom (.read (var "c")))) }

def aliased : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1)) (.call 0 [] [(.mut, var "x"), (.ro, deref (var "x"))])

example : (eval [clobber] [] 20 [] empty [] aliased).1 = .stuck := by decide

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
    (.handle (.let_ "a" .int (.perform 0 [] []) (.add (.read (var "a")) (.read (deref (var "base"))))) 0
      [⟨"b", .ro, .int, deref (var "base")⟩] [] []
      (.add (.read (var "b")) (.lit 1)))

example : (eval [] ops 20 [] .empty [] asks).1 = .val (.int 81) := by decide
example : ∀ l < (eval [] ops 20 [] .empty [] asks).2.next, (eval [] ops 20 [] .empty [] asks).2.mem l = none := by
  decide

theorem asks_typed : Typed [] ops [] asks .int [] [.fail] := by
  refine .let_ (live := true) rfl (.new .lit) ?_
  have := Typed.handle (F := []) (O := ops) (Γ := [("base", .own (.box .int) true)]) (e := 0) (op := ops[0])
    (os := []) (rs := []) (caps := [⟨"b", .ro, .int, deref (var "base")⟩]) (ys := [(.ro, "base")]) (r := [.fail])
    (arm := .add (.read (var "b")) (.lit 1)) (Γa := [("b", .ref .ro .int)])
    (body := .let_ "a" .int (.perform 0 [] []) (.add (.read (var "a")) (.read (deref (var "base"))))) (τ := .int)
    (Γb := [("base", .ref .ro (.box .int))])
    rfl rfl rfl (.ro (.deref (.own rfl)) .nil) (by simp [Exclusive]) (by decide)
    (.add (.read (.ref rfl)) .lit)
    (.let_ rfl (.perform (op := { owns := [], refs := [], ret := .int }) rfl (List.mem_cons_self ..) .nil .nil
      List.Pairwise.nil) (.add (.read (.own rfl)) (.read (.deref (.ref rfl)))))
  simpa [thaw, unhideAll, hideAll, roots] using this

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
    (.handle (.let_ "t" (.box .int) (.new (.lit 2))
        (.let_ "u" .int (.assign (var "x") (.box .int) (.move "t")) (.perform 0 [] []))) 0
      [⟨"b", .ro, .int, deref (var "x")⟩] [] [] (.atom (.read (var "b"))))

/-- A variable that may be changed through is owned and live, or a `mut` borrow. -/
theorem var_writable (h : PlaceTy Γ (var x) τ w y) (hw : w = true) :
    lookup x Γ = some (.own τ true) ∨ lookup x Γ = some (.ref .mut τ) := by
  cases h with
  | own hx => exact .inl hx
  | ref hx =>
    rename_i m
    cases m with
    | ro => simp at hw
    | «mut» => exact .inr hx

/-- What a `handle` lends its arm, and its body, typed where those places lent `readonly` are only
read and those lent `mut` out of reach. -/
theorem handle_inv : Typed F O Γ (.handle body e caps os rs arm) τ Γ' r →
    ∃ ys Γb, Caps Γ caps ys ∧ Typed F O (freeze (hideAll Γ (roots .mut ys)) (roots .ro ys)) body τ Γb (.eff e :: r) := by
  intro h
  cases h with
  | handle _ _ _ hc _ _ _ hb => exact ⟨_, _, hc, hb⟩

theorem clobbers_rejected : ¬ Typed [] ops [] clobbers τ Γ' r := by
  intro h
  cases h with
  | let_ _ h0 hb =>
    cases h0 with
    | new h0 =>
    cases h0
    obtain ⟨ys, Γb, hc, hbody⟩ := handle_inv hb
    cases hc with
    | ro hp hc =>
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
              rcases var_writable hp' rfl with h | h <;> simp [lookup, freeze, hideAll, setSlot, Slot.ro] at h

/-- `let n = 0; (handle { Ask.ask() + Ask.ask() } with Ask { ask() resumes k => { c = c + 1; k(c) } }) + n`,
the arm lent `n` as `c`, `mut`: state an arm keeps from one operation to the next, which the body
cannot reach while the `handle` runs. The operations give 1 and 2, and `n` is 2 after; 5. -/
def counts : Expr :=
  .let_ "n" .int (.atom (.lit 0))
    (.let_ "h" .int
      (.handle (.let_ "a" .int (.perform 0 [] []) (.let_ "b" .int (.perform 0 [] []) (.add (.read (var "a")) (.read (var "b")))))
        0 [⟨"c", .mut, .int, var "n"⟩] [] []
        (.let_ "t" .int (.add (.read (var "c")) (.lit 1)) (.let_ "u" .int (.write (var "c") (.read (var "t")))
          (.atom (.read (var "c"))))))
      (.add (.read (var "h")) (.read (var "n"))))

example : (eval [] ops 20 [] .empty [] counts).1 = .val (.int 5) := by decide
example : ∀ l < (eval [] ops 20 [] .empty [] counts).2.next, (eval [] ops 20 [] .empty [] counts).2.mem l = none := by
  decide

theorem counts_typed : Typed [] ops [] counts .int [] [.fail] := by
  have := Typed.handle (F := []) (O := ops) (Γ := [("n", .own .int true)]) (e := 0) (op := ops[0])
    (os := []) (rs := []) (caps := [⟨"c", .mut, .int, var "n"⟩]) (ys := [(.mut, "n")]) (r := [.fail])
    (arm := .let_ "t" .int (.add (.read (var "c")) (.lit 1)) (.let_ "u" .int (.write (var "c") (.read (var "t")))
      (.atom (.read (var "c")))))
    (Γa := [("c", .ref .mut .int)])
    (body := .let_ "a" .int (.perform 0 [] []) (.let_ "b" .int (.perform 0 [] []) (.add (.read (var "a")) (.read (var "b")))))
    (τ := .int) (Γb := [("n", .lent .int)])
    rfl rfl rfl (.mut (.own rfl) .nil) (by simp [Exclusive]) (by decide)
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
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (fun _ h => by simp at h) counts_typed

/-- `let n = 0; handle { n = 5; Ask.ask() } with Ask { ask() resumes k => { c = c + 1; k(c) } }`: the
body changes the state its arm was lent `mut`. The types reject it: what an arm keeps, the body
cannot reach. -/
def meddles : Expr :=
  .let_ "n" .int (.atom (.lit 0))
    (.handle (.let_ "u" .int (.write (var "n") (.lit 5)) (.perform 0 [] [])) 0 [⟨"c", .mut, .int, var "n"⟩] [] []
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
    | «mut» hp hc =>
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

example : (eval [] [] 20 [] .empty [] cleans).1 = .val (.int 7) := by decide
example : ∀ l < (eval [] [] 20 [] .empty [] cleans).2.next, (eval [] [] 20 [] .empty [] cleans).2.mem l = none := by
  decide

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

example : (eval [] [] 20 [] .empty [] borrows).1 = .val (.int 42) := by decide
example : ∀ l < (eval [] [] 20 [] .empty [] borrows).2.next, (eval [] [] 20 [] .empty [] borrows).2.mem l = none := by
  decide

theorem borrows_typed : Typed [] [] [] borrows .int [] [.fail] := by
  have := Typed.lend (F := []) (O := []) (Γ := [("x", .own (.box .int) true)]) (x := "r") (m := .mut)
    (p := deref (var "x")) (τ := .int) (w := true) (y := "x") (r := [.fail])
    (body := .let_ "t" .int (.add (.read (var "r")) (.lit 41)) (.write (var "r") (.read (var "t")))) (τb := .int)
    (Γb := [("x", .lent (.box .int))]) rfl (.deref (.own rfl)) (fun _ => rfl)
    (.let_ (live := true) rfl (.add (.read (.ref rfl)) .lit) (.write (.read (.own rfl)) (.ref (m := .mut) rfl)))
  simp only [thaw] at this
  exact .let_ (live := true) rfl (.new .lit) (.let_ (live := true) rfl (by simpa using this)
    (.atom (.read (.deref (.own rfl)))))

/-- `let x = Box.new(20); { const r = readonly x; *r + *x }`: a `readonly` borrow and what it
borrows, both read; 40. -/
def reads : Expr :=
  .let_ "x" (.box .int) (.new (.lit 20))
    (.lend "r" .ro (var "x") (.add (.read (deref (var "r"))) (.read (deref (var "x")))))

example : (eval [] [] 20 [] .empty [] reads).1 = .val (.int 40) := by decide

/-- `let x = Box.new(1); { const r = mut *x; *x }`: `x` reached while lent `mut`. The types reject
it: nothing may reach what a `mut` borrow has while it lives. -/
def reaches : Expr :=
  .let_ "x" (.box .int) (.new (.lit 1)) (.lend "r" .mut (deref (var "x")) (.atom (.read (deref (var "x")))))

/-- What a borrow is of, and the code it is in scope for, typed with its root out of reach. -/
theorem lend_inv : Typed F O Γ (.lend x m p body) τ Γ' r →
    ∃ τp w y Γb, PlaceTy Γ p τp w y ∧ Typed F O ((x, .ref m τp) :: lendCtx m Γ y) body τ ((x, .ref m τp) :: Γb) r := by
  intro h
  cases h with
  | lend _ hp _ hb => exact ⟨_, _, _, _, hp, hb⟩

theorem reaches_rejected : ¬ Typed [] O [] reaches τ Γ' r := by
  intro h
  cases h with
  | let_ _ _ hb =>
    obtain ⟨τp, w, y, Γb, hp, hbody⟩ := lend_inv hb
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

end FlyCore.Ownership.Examples
