import FlyCore.OwnershipExamples

/-!
Atomics, channels and `Mutex` are handlers that own their state around a scope whose tasks perform
their operations. An arm runs whole between two operations of the tasks, so each operation takes
effect at one point among all of theirs, in the order the schedule picks: sequential consistency.
What a task sends or unlocks moves into the handler's state, and what another receives or locks
moves out to it, so a value is owned by one task at a time. The theorems below hold under every
schedule, with running tasks stopped for others before any of their operations.
-/

namespace FlyCore.Ownership.Concurrency

open Expr Place Examples

set_option linter.unusedSimpArgs false

/-- `run`, for programs whose runs take more rewriting steps. -/
syntax "runLong" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| runLong [$xs,*]) => `(tactic| simp (config := { maxSteps := 20000000 }) [eval, evalS, IntOp.apply, preTarget, ret, evalK,
      flushR, flush, andThen, konts, kontsK, cellKonts, cellsKonts, evalAtom, evalAtoms, resolve, leave, cleanV,
      cleanA, dropRet, armEnd, callRet, allocAll, dropCells, dropCell, drop, dropK, pick, Store.fresh, Store.alloc, Store.set, find,
      Frame.handles, Kont.push, lookup, Res.done, Outcome.res, Cap.at, Store.empty, Store.sched0, value, freed, freedBelow,
      Store.tag, Store.freeAll, Store.moveAll, dropCellsWith, fiberHS, hsConv, hsDie, dedupL, cellTree, treeK,
      Val.tree, kfoot, Val.foot, dropAll, kontsAll, isStuck, $xs,*])

/-- A task's closure: `(_) => body`, having captured an integer it ignores. -/
def task (row : Row) (body : Expr) : Fn :=
  { owns := [("p", .int)], refs := [], ret := .int, row := row, cap := some ("z", .int, .once), body := body }

/-! ## Atomics

`Atomic<int>`: `rmw(kind, a, b)` gives the integer held before it and, by `kind`, adds `a` to it
(`fetchAdd`, and `load` as `fetchAdd(0)`), puts `b` in its place where it plus `a` is 0
(`compareExchange` of `-a` for `b`), or puts `b` in its place (`store`, `swap`). -/

def atSpawn : Op := { owns := [.fn .once .int .int [.eff 0, .eff 2] .nil], refs := [], ret := .int }
def atRmw : Op := { owns := [.int, .int, .int], refs := [], ret := .int }
def atOps : List Op := [scYield, atSpawn, atRmw]

/-- The arm, lent the integer as `c`, `mut`. -/
def atArm : Expr :=
  .let_ "o" .int (.atom (.read (var "c")))
    (.let_ "u" .int
      (.ite (.read (var "k"))
        (.let_ "k1" .int (.add (.read (var "k")) (.lit (-1)))
          (.ite (.read (var "k1"))
            (.write (var "c") (.read (var "b")))
            (.let_ "d" .int (.add (.read (var "o")) (.read (var "a")))
              (.ite (.read (var "d")) (.atom (.lit 0)) (.write (var "c") (.read (var "b")))))))
        (.let_ "s" .int (.add (.read (var "o")) (.read (var "a"))) (.write (var "c") (.read (var "s")))))
      (.atom (.read (var "o"))))

def fetchAdd (x : Var) (a : Int) (rest : Expr) : Expr := .let_ x .int (.perform 2 [.lit 0, .lit a, .lit 0] []) rest
def cas (x : Var) (expected new : Int) (rest : Expr) : Expr :=
  .let_ x .int (.perform 2 [.lit 1, .lit (-expected), .lit new] []) rest
def yield_ (x : Var) (rest : Expr) : Expr := .let_ x .int (.perform 0 [] []) rest

/-- `(_) => { n.fetchAdd(1); yield; n.fetchAdd(1); 0 }` -/
def incTk : Fn := task [.eff 0, .eff 2] (fetchAdd "a" 1 (yield_ "y" (fetchAdd "b" 1 (.atom (.lit 0)))))

/-- `const n = new Atomic(0); scope((s) => { s.spawn(inc); s.spawn(inc); n.compareExchange(0, 10);
yield; n.fetchAdd(1) }); n.load()`: two tasks and the body change one integer at once. -/
def atomicEx : Expr :=
  .let_ "n" .int (.atom (.lit 0))
    (.handle .int
      (.let_ "u" .int
        (.scope 0 1 [] .int
          (.let_ "k" (.fn .once .int .int [.eff 0, .eff 2] .nil) (.lam 0 (.lit 0))
            (.let_ "s1" .int (.perform 1 [.move "k"] [])
              (.let_ "k2" (.fn .once .int .int [.eff 0, .eff 2] .nil) (.lam 0 (.lit 0))
                (.let_ "s2" .int (.perform 1 [.move "k2"] [])
                  (cas "c1" 0 10 (yield_ "y" (fetchAdd "f" 1 (.atom (.lit 0))))))))))
        (fetchAdd "r" 0 (.atom (.read (var "r")))))
      2 [⟨"c", .mut, .int, var "n"⟩] ["k", "a", "b"] [] atArm)

theorem incTk_ok : FnsOk [incTk] atOps := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  refine ⟨by decide, ?_⟩
  simp only [incTk, task, fetchAdd, yield_, FnOk, fnCtx, cloFn, ownCtx, refCtx]
  refine ⟨by decide, [("p", .own .int true), ("z", .own .int true)], ?_⟩
  refine .let_ (live := true) rfl (.perform (op := atRmw) rfl (by simp) (.cons .lit (.cons .lit (.cons .lit .nil))) .nil .nil) ?_
  refine .let_ (live := true) rfl (.perform (op := scYield) rfl (by simp) .nil .nil .nil) ?_
  exact .let_ (live := true) rfl (.perform (op := atRmw) rfl (by simp) (.cons .lit (.cons .lit (.cons .lit .nil))) .nil .nil)
    (.atom .lit)

theorem atArm_typed : Typed [incTk] atOps (armCtx ["k", "a", "b"] [] atRmw [("c", .mut, .int)]) atArm .int
    (armCtx ["k", "a", "b"] [] atRmw [("c", .mut, .int)]) [.fail] := by
  simp only [armCtx, atRmw, List.zip, List.zipWith, List.map, List.append_nil, List.cons_append, List.nil_append]
  refine .let_ (live := true) rfl (.atom (.read (.ref rfl))) ?_
  refine .let_ (live := true) rfl (.ite (.read (.own rfl)) ?_ ?_ (Weaker.refl _) (Weaker.refl _)) (.atom (.read (.own rfl)))
  · refine .let_ (live := true) rfl (.add (.read (.own rfl)) .lit) ?_
    refine .ite (.read (.own rfl)) (.write (.read (.own rfl)) (.ref (m := .mut) rfl)) ?_ (Weaker.refl _) (Weaker.refl _)
    refine .let_ (live := true) rfl (.add (.read (.own rfl)) (.read (.own rfl))) ?_
    exact .ite (.read (.own rfl)) (.atom .lit) (.write (.read (.own rfl)) (.ref (m := .mut) rfl)) (Weaker.refl _) (Weaker.refl _)
  · exact .let_ (live := true) rfl (.add (.read (.own rfl)) (.read (.own rfl)))
      (.write (.read (.own rfl)) (.ref (m := .mut) rfl))

theorem atomicEx_typed : Typed [incTk] atOps [] atomicEx .int [] [.fail] := by
  have hs : Typed [incTk] atOps [("n", .lent .int false)]
      (.scope 0 1 [] .int
          (.let_ "k" (.fn .once .int .int [.eff 0, .eff 2] .nil) (.lam 0 (.lit 0))
            (.let_ "s1" .int (.perform 1 [.move "k"] [])
              (.let_ "k2" (.fn .once .int .int [.eff 0, .eff 2] .nil) (.lam 0 (.lit 0))
                (.let_ "s2" .int (.perform 1 [.move "k2"] [])
                  (cas "c1" 0 10 (yield_ "y" (fetchAdd "f" 1 (.atom (.lit 0))))))))))
      .int [("n", .lent .int false)] [.eff 2, .fail] := by
    refine .scope (op := scYield) (opS := atSpawn) (rT := [.eff 0, .eff 2]) rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
      (by simp) (by simp) (by decide) rfl (by simp) ?_
    refine .let_ (live := false) rfl (.lam (d := incTk) rfl rfl rfl rfl rfl .lit rfl) ?_
    refine .let_ (live := true) rfl (.perform (op := atSpawn) rfl (by simp) (.cons (.move rfl rfl) .nil) .nil .nil) ?_
    refine .let_ (live := false) rfl (.lam (d := incTk) rfl rfl rfl rfl rfl .lit rfl) ?_
    refine .let_ (live := true) rfl (.perform (op := atSpawn) rfl (by simp) (.cons (.move rfl rfl) .nil) .nil .nil) ?_
    refine .let_ (live := true) rfl (.perform (op := atRmw) rfl (by simp) (.cons .lit (.cons .lit (.cons .lit .nil))) .nil .nil) ?_
    refine .let_ (live := true) rfl (.perform (op := scYield) rfl (by simp) .nil .nil .nil) ?_
    exact .let_ (live := true) rfl (.perform (op := atRmw) rfl (by simp) (.cons .lit (.cons .lit (.cons .lit .nil))) .nil .nil)
      (.atom .lit)
  have := Typed.handle (F := [incTk]) (O := atOps) (Γ := [("n", .own .int true)]) (e := 2) (op := atRmw)
    (os := ["k", "a", "b"]) (rs := []) (caps := [⟨"c", .mut, .int, var "n"⟩]) (ys := [(.mut, "n")]) (r := [.fail])
    (Γb := [("n", .lent .int false)]) (τ := .int) (arm := atArm)
    (body := .let_ "u" .int (.scope 0 1 [] .int
          (.let_ "k" (.fn .once .int .int [.eff 0, .eff 2] .nil) (.lam 0 (.lit 0))
            (.let_ "s1" .int (.perform 1 [.move "k"] [])
              (.let_ "k2" (.fn .once .int .int [.eff 0, .eff 2] .nil) (.lam 0 (.lit 0))
                (.let_ "s2" .int (.perform 1 [.move "k2"] [])
                  (cas "c1" 0 10 (yield_ "y" (fetchAdd "f" 1 (.atom (.lit 0))))))))))
        (fetchAdd "r" 0 (.atom (.read (var "r")))))
    rfl rfl (by simp [atRmw]; rfl) rfl rfl (.mut (.own rfl) rfl rfl .nil) (by simp [Exclusive]) (by decide)
    atArm_typed
    (by
      refine .let_ (live := true) rfl hs ?_
      exact .let_ (live := true) rfl (.perform (op := atRmw) rfl (by simp) (.cons .lit (.cons .lit (.cons .lit .nil))) .nil .nil)
        (.atom (.read (.own rfl))))
  simp [thaw, unhideAll, hideAll, hide, roots, Slot.ty] at this
  exact .let_ (live := true) rfl (.atom .lit) this

/-- Under any schedule. -/
theorem atomicEx_ok (s p : Nat → Bool) : ∀ n, match eval [incTk] atOps n [.abort .fail 0] (Store.sched0 s p) [] atomicEx with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [incTk] ⟨[], Wstar [incTk] atOps⟩ σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok_sched incTk_ok atomicEx_typed s p

set_option maxHeartbeats 4000000 in
example : value (eval [incTk] atOps 200 [] .empty [] atomicEx) = some 15 := by
  run [atomicEx, incTk, task, atOps, atArm, atRmw, atSpawn, scYield, fetchAdd, cas, yield_, mkTask, cloFn]
set_option maxHeartbeats 4000000 in
example : freed (eval [incTk] atOps 200 [] .empty [] atomicEx) := by
  run [atomicEx, incTk, task, atOps, atArm, atRmw, atSpawn, scYield, fetchAdd, cas, yield_, mkTask, cloFn]
set_option maxHeartbeats 4000000 in
/-- The tasks change the integer first, and the body's `compareExchange` finds 2, not 0. -/
example : value (eval [incTk] atOps 200 [] (Store.sched0 (fun _ => false) fun i => i % 3 == 1) [] atomicEx) = some 5 := by
  run [atomicEx, incTk, task, atOps, atArm, atRmw, atSpawn, scYield, fetchAdd, cas, yield_, mkTask, cloFn]

/-! ## Channels

A channel of boxes: `msg(#Send(b))` moves the box `b` in and gives `#Ok`, `msg(#Recv)` gives
`#Empty` or `#Some(b)`, the box moved out, first in first out. The arm keeps two stacks: what is
sent is pushed on `qi`; a receive pops `qo`, first moving all of `qi` onto it where it is empty. -/

def chMsgT : Ty := .sum (.box .int) .int
def chRetT : Ty := .sum .int (.box .int)
def chSpawn : Op := { owns := [.fn .once .int .int [.eff 0, .eff 2] .nil], refs := [], ret := .int }
def chMsg : Op := { owns := [chMsgT], refs := [], ret := chRetT }
def chOps : List Op := [scYield, chSpawn, chMsg]
def boxes : Ty := .vec true (.box .int)

/-- `while (g) { const t = qi.pop(); match t { #Empty => g = 0, #Some(x) => qo.push(x) } }` -/
def refill : Expr :=
  .while_ (.atom (.read (var "g")))
    (.let_ "t" (.sum .int (.box .int)) (.vpop (var "qi"))
      (.case "t" "x" .int (.box .int) (.write (var "g") (.lit 0)) (.vpush (var "qo") (.move "x"))))

/-- The arm, lent the stacks as `qi` and `qo`, `mut`. -/
def chArm : Expr :=
  .case "m" "y" (.box .int) .int
    (.let_ "u" .int (.vpush (var "qi") (.move "y")) (.inj .int (.box .int) true (.lit 0)))
    (.let_ "n" .int (.vlen (var "qo"))
      (.ite (.read (var "n")) (.vpop (var "qo"))
        (.let_ "g" .int (.atom (.lit 1)) (.let_ "w" .int refill (.vpop (var "qo"))))))

def send (b m r : Var) (v : Int) (rest : Expr) : Expr :=
  .let_ b (.box .int) (.new (.lit v))
    (.let_ m chMsgT (.inj (.box .int) .int true (.move b)) (.let_ r chRetT (.perform 2 [.move m] []) rest))

/-- `(_) => { ch.send(Box.new(10)); yield; ch.send(Box.new(20)); ch.send(Box.new(12)); 0 }` -/
def producer : Fn := task [.eff 0, .eff 2] (send "b1" "m1" "r1" 10 (yield_ "y" (send "b2" "m2" "r2" 20 (send "b3" "m3" "r3" 12 (.atom (.lit 0))))))

/-- `match ch.recv() { #Empty => yield, #Some(b) => { acc = acc + acc + *b; rem = rem - 1 } }` -/
def recvStep : Expr :=
  .let_ "m" chMsgT (.inj (.box .int) .int false (.lit 0))
    (.let_ "r" chRetT (.perform 2 [.move "m"] [])
      (.case "r" "y" .int (.box .int)
        (yield_ "u" (.atom (.lit 0)))
        (.let_ "a2" .int (.add (.read (var "acc")) (.read (var "acc")))
          (.let_ "s" .int (.add (.read (var "a2")) (.read (deref (var "y"))))
            (.let_ "u" .int (.write (var "acc") (.read (var "s")))
              (.let_ "t" .int (.add (.read (var "rem")) (.lit (-1))) (.write (var "rem") (.read (var "t")))))))))

/-- `scope((s) => { s.spawn(producer); let rem = 3, acc = 0; while (rem) recvStep; acc })` -/
def chScope : Expr :=
  .scope 0 1 [] .int
    (.let_ "k" (.fn .once .int .int [.eff 0, .eff 2] .nil) (.lam 0 (.lit 0))
      (.let_ "s0" .int (.perform 1 [.move "k"] [])
        (.let_ "rem" .int (.atom (.lit 3))
          (.let_ "acc" .int (.atom (.lit 0))
            (.let_ "w" .int (.while_ (.atom (.read (var "rem"))) recvStep) (.atom (.read (var "acc"))))))))

/-- A task sends three boxes over a channel, which the scope's body receives as they come, giving
way while there is none: 92, `((10 · 2) + 20) · 2 + 12`, the boxes received in the order sent,
whichever way the two interleave, and every box freed, as each was owned by one task at a time. -/
def chanEx : Expr :=
  .let_ "qi" boxes .vnew (.let_ "qo" boxes .vnew
    (.handle .int chScope 2 [⟨"qi", .mut, boxes, var "qi"⟩, ⟨"qo", .mut, boxes, var "qo"⟩] ["m"] [] chArm))

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
example : value (eval [producer] chOps 400 [] (Store.sched0 fun _ => false) [] chanEx) = some 92 := by
  runLong [chanEx, chScope, recvStep, refill, chArm, send, producer, task, chOps, chMsg, chSpawn, scYield, yield_, boxes,
    chMsgT, chRetT, mkTask, cloFn]
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
example : value (eval [producer] chOps 400 [] (Store.sched0 (fun _ => false) fun i => i % 3 == 1) [] chanEx) = some 92 := by
  runLong [chanEx, chScope, recvStep, refill, chArm, send, producer, task, chOps, chMsg, chSpawn, scYield, yield_, boxes,
    chMsgT, chRetT, mkTask, cloFn]
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
example : freed (eval [producer] chOps 400 [] (Store.sched0 (fun _ => false) fun i => i % 3 == 1) [] chanEx) := by
  runLong [chanEx, chScope, recvStep, refill, chArm, send, producer, task, chOps, chMsg, chSpawn, scYield, yield_, boxes,
    chMsgT, chRetT, mkTask, cloFn]

theorem producer_ok : FnsOk [producer] chOps := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  refine ⟨by decide, ?_⟩
  simp only [producer, task, send, yield_, FnOk, fnCtx, cloFn, ownCtx, refCtx]
  refine ⟨by decide, [("p", .own .int true), ("z", .own .int true)], ?_⟩
  refine .let_ (live := false) rfl (.new .lit) ?_
  refine .let_ (live := false) rfl (.inj (.move rfl rfl) rfl) ?_
  refine .let_ (live := true) rfl (.perform (op := chMsg) rfl (by simp) (.cons (.move rfl rfl) .nil) .nil .nil) ?_
  refine .let_ (live := true) rfl (.perform (op := scYield) rfl (by simp) .nil .nil .nil) ?_
  refine .let_ (live := false) rfl (.new .lit) ?_
  refine .let_ (live := false) rfl (.inj (.move rfl rfl) rfl) ?_
  refine .let_ (live := true) rfl (.perform (op := chMsg) rfl (by simp) (.cons (.move rfl rfl) .nil) .nil .nil) ?_
  refine .let_ (live := false) rfl (.new .lit) ?_
  refine .let_ (live := false) rfl (.inj (.move rfl rfl) rfl) ?_
  exact .let_ (live := true) rfl (.perform (op := chMsg) rfl (by simp) (.cons (.move rfl rfl) .nil) .nil .nil) (.atom .lit)

/-- The arm's context once `m` is taken apart. -/
def chΓm : Ctx := [("m", .own chMsgT false), ("qi", .ref .mut boxes), ("qo", .ref .mut boxes)]

theorem refill_typed : Typed F O (("g", .own .int true) :: ("n", .own .int true) :: ("y", .own .int true) :: chΓm) refill .int
    (("g", .own .int true) :: ("n", .own .int true) :: ("y", .own .int true) :: chΓm) r := by
  refine .while_ (.atom (.read (.own rfl))) ?_
  refine .let_ (live := false) rfl (.vpop (.ref (m := .mut) rfl) rfl) ?_
  exact .case (Γ₁ := ("t", .own (.sum .int (.box .int)) false) :: ("g", .own .int true) :: ("n", .own .int true) ::
      ("y", .own .int true) :: chΓm)
    (Γ₂ := ("t", .own (.sum .int (.box .int)) false) :: ("g", .own .int true) :: ("n", .own .int true) ::
      ("y", .own .int true) :: chΓm) (l₁ := true) (l₂ := false) rfl rfl rfl
    (.write .lit (.own rfl)) (.vpush (.move rfl rfl) (.ref (m := .mut) rfl)) (Weaker.refl _) (Weaker.refl _)

theorem chArm_typed : Typed F O (armCtx ["m"] [] chMsg [("qi", .mut, boxes), ("qo", .mut, boxes)]) chArm chRetT chΓm r := by
  refine .case (Γ₁ := chΓm) (Γ₂ := chΓm) (l₁ := false) (l₂ := true) rfl rfl rfl ?_ ?_ (Weaker.refl _) (Weaker.refl _)
  · exact .let_ (live := true) rfl (.vpush (.move rfl rfl) (.ref (m := .mut) rfl)) (.inj .lit rfl)
  · refine .let_ (live := true) rfl (.vlen (.ref rfl)) (.ite (.read (.own rfl)) (.vpop (.ref (m := .mut) rfl) rfl) ?_ (Weaker.refl _) (Weaker.refl _))
    exact .let_ (live := true) rfl (.atom .lit) (.let_ (live := true) rfl refill_typed (.vpop (.ref (m := .mut) rfl) rfl))

/-- What the `handle`'s body has of the code around: the stacks, out of its reach. -/
def chH : Ctx := [("qo", .lent boxes false), ("qi", .lent boxes false)]
def chRS : Ctx := [("acc", .own .int true), ("rem", .own .int true), ("s0", .own .int true),
  ("k", .own (.fn .once .int .int [.eff 0, .eff 2] .nil) false)] ++ chH

theorem recvStep_typed : Typed [producer] chOps chRS recvStep .int chRS [.eff 0, .eff 1, .eff 2, .fail] := by
  refine .let_ (live := false) rfl (.inj .lit rfl) ?_
  refine .let_ (live := false) rfl (.perform (op := chMsg) rfl (by simp) (.cons (.move rfl rfl) .nil) .nil .nil) ?_
  refine .case (Γ₁ := ("r", .own chRetT false) :: ("m", .own chMsgT false) :: chRS)
    (Γ₂ := ("r", .own chRetT false) :: ("m", .own chMsgT false) :: chRS) (l₁ := true) (l₂ := true) rfl rfl rfl ?_ ?_
    (Weaker.refl _) (Weaker.refl _)
  · exact .let_ (live := true) rfl (.perform (op := scYield) rfl (by simp) .nil .nil .nil) (.atom .lit)
  · refine .let_ (live := true) rfl (.add (.read (.own rfl)) (.read (.own rfl))) ?_
    refine .let_ (live := true) rfl (.add (.read (.own rfl)) (.read (.deref (.own rfl)))) ?_
    refine .let_ (live := true) rfl (.write (.read (.own rfl)) (.own rfl)) ?_
    exact .let_ (live := true) rfl (.add (.read (.own rfl)) .lit) (.write (.read (.own rfl)) (.own rfl))

theorem chScope_typed : Typed [producer] chOps chH chScope .int chH [.eff 2, .fail] := by
  refine .scope (op := scYield) (opS := chSpawn) (rT := [.eff 0, .eff 2]) rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
    (by simp) (by simp) (by decide) rfl (by simp) ?_
  refine .let_ (live := false) rfl (.lam (d := producer) rfl rfl rfl rfl rfl .lit rfl) ?_
  refine .let_ (live := true) rfl (.perform (op := chSpawn) rfl (by simp) (.cons (.move rfl rfl) .nil) .nil .nil) ?_
  refine .let_ (live := true) rfl (.atom .lit) ?_
  refine .let_ (live := true) rfl (.atom .lit) ?_
  exact .let_ (live := true) rfl (.while_ (.atom (.read (.own rfl))) recvStep_typed) (.atom (.read (.own rfl)))

theorem chanEx_typed : Typed [producer] chOps [] chanEx .int [] [.fail] := by
  refine .let_ (live := true) rfl (.vnew rfl) (.let_ (live := true) rfl (.vnew rfl) ?_)
  have := Typed.handle (F := [producer]) (O := chOps) (Γ := [("qo", .own boxes true), ("qi", .own boxes true)]) (e := 2)
    (op := chMsg) (os := ["m"]) (rs := []) (caps := [⟨"qi", .mut, boxes, var "qi"⟩, ⟨"qo", .mut, boxes, var "qo"⟩])
    (ys := [(.mut, "qi"), (.mut, "qo")]) (r := [.fail]) (Γb := chH) (τ := .int) (arm := chArm) (body := chScope)
    rfl rfl (by simp [chMsg, chMsgT]; rfl) rfl rfl (.mut (.own rfl) rfl rfl (.mut (.own rfl) rfl rfl .nil))
    (by simp [Exclusive]) (by decide) chArm_typed chScope_typed
  simpa [thaw, unhideAll, hideAll, hide, roots, Slot.ty, chH] using this

/-- Under any schedule. -/
theorem chanEx_ok (s p : Nat → Bool) : ∀ n, match eval [producer] chOps n [.abort .fail 0] (Store.sched0 s p) [] chanEx with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [producer] ⟨[], Wstar [producer] chOps⟩ σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok_sched producer_ok chanEx_typed s p

/-! ## Mutex

`Mutex<Box<int>>`: the handler's state holds the box while it is unlocked. `msg(#Lock)` gives
`#Busy`, or `#Some(b)`, the box moved out to the task that locked it, the one task that can reach it
until it unlocks; `msg(#Unlock(b))` moves it back. The messages are the channel's. -/

/-- The arm, lent the state as `st`, `mut`. -/
def mxArm : Expr :=
  .case "m" "y" (.box .int) .int
    (.let_ "u" .int (.vpush (var "st") (.move "y")) (.inj .int (.box .int) true (.lit 0)))
    (.vpop (var "st"))

/-- `while (want) match mx.lock() { #Busy => yield, #Some(g) => { const x = *g; yield; *g = x + z;
mx.unlock(g); want = 0 } }`: the read and the write of the guarded integer with a yield between, which
would lose an update if another task could reach it meanwhile. -/
def lockStep : Expr :=
  .let_ "m" chMsgT (.inj (.box .int) .int false (.lit 0))
    (.let_ "r" chRetT (.perform 2 [.move "m"] [])
      (.case "r" "g" .int (.box .int)
        (yield_ "u" (.atom (.lit 0)))
        (.let_ "x" .int (.atom (.read (deref (var "g"))))
          (yield_ "u" (.let_ "x2" .int (.add (.read (var "x")) (.read (var "z")))
            (.let_ "u2" .int (.write (deref (var "g")) (.read (var "x2")))
              (.let_ "m2" chMsgT (.inj (.box .int) .int true (.move "g"))
                (.let_ "r2" chRetT (.perform 2 [.move "m2"] []) (.write (var "want") (.lit 0))))))))))

/-- `(_) => { let want = 1; while (want) lockStep; 0 }`, having captured `z`, what it adds. -/
def adder : Fn :=
  { owns := [("p", .int)], refs := [], ret := .int, row := [.eff 0, .eff 2], cap := some ("z", .int, .once),
    body := .let_ "want" .int (.atom (.lit 1)) (.let_ "w" .int (.while_ (.atom (.read (var "want"))) lockStep) (.atom (.lit 0))) }

/-- `const mx = new Mutex(Box.new(0)); scope((s) => { s.spawn(() => add(20)); s.spawn(() => add(22));
yield; 0 }); *mx.lock()`: 42, whichever way the tasks interleave. -/
def mutexEx : Expr :=
  .let_ "st" boxes .vnew
    (.let_ "b0" (.box .int) (.new (.lit 0))
      (.let_ "u0" .int (.vpush (var "st") (.move "b0"))
        (.let_ "h" .int
          (.handle .int
            (.scope 0 1 [] .int
              (.let_ "k" (.fn .once .int .int [.eff 0, .eff 2] .nil) (.lam 0 (.lit 20))
                (.let_ "s1" .int (.perform 1 [.move "k"] [])
                  (.let_ "k2" (.fn .once .int .int [.eff 0, .eff 2] .nil) (.lam 0 (.lit 22))
                    (.let_ "s2" .int (.perform 1 [.move "k2"] []) (yield_ "y" (.atom (.lit 0))))))))
            2 [⟨"st", .mut, boxes, var "st"⟩] ["m"] [] mxArm)
          (.let_ "r" chRetT (.vpop (var "st"))
            (.case "r" "g" .int (.box .int) (.atom (.lit (-1))) (.atom (.read (deref (var "g")))))))))

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
example : value (eval [adder] chOps 600 [] (Store.sched0 fun _ => false) [] mutexEx) = some 42 := by
  runLong [mutexEx, lockStep, adder, mxArm, chOps, chMsg, chSpawn, scYield, yield_, boxes, chMsgT, chRetT, mkTask, cloFn]
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
example : value (eval [adder] chOps 600 [] (Store.sched0 (fun _ => false) fun i => i % 3 == 1) [] mutexEx) = some 42 := by
  runLong [mutexEx, lockStep, adder, mxArm, chOps, chMsg, chSpawn, scYield, yield_, boxes, chMsgT, chRetT, mkTask, cloFn]
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
example : freed (eval [adder] chOps 600 [] (Store.sched0 (fun _ => false) fun i => i % 3 == 1) [] mutexEx) := by
  runLong [mutexEx, lockStep, adder, mxArm, chOps, chMsg, chSpawn, scYield, yield_, boxes, chMsgT, chRetT, mkTask, cloFn]

def mxLW : Ctx := [("want", .own .int true), ("p", .own .int true), ("z", .own .int true)]

theorem lockStep_typed : Typed [adder] chOps mxLW lockStep .int mxLW [.eff 0, .eff 2] := by
  refine .let_ (live := false) rfl (.inj .lit rfl) ?_
  refine .let_ (live := false) rfl (.perform (op := chMsg) rfl (by simp) (.cons (.move rfl rfl) .nil) .nil .nil) ?_
  refine .case (Γ₁ := ("r", .own chRetT false) :: ("m", .own chMsgT false) :: mxLW)
    (Γ₂ := ("r", .own chRetT false) :: ("m", .own chMsgT false) :: mxLW) (l₁ := true) (l₂ := false) rfl rfl rfl ?_ ?_
    (Weaker.refl _) (Weaker.refl _)
  · exact .let_ (live := true) rfl (.perform (op := scYield) rfl (by simp) .nil .nil .nil) (.atom .lit)
  · refine .let_ (live := true) rfl (.atom (.read (.deref (.own rfl)))) ?_
    refine .let_ (live := true) rfl (.perform (op := scYield) rfl (by simp) .nil .nil .nil) ?_
    refine .let_ (live := true) rfl (.add (.read (.own rfl)) (.read (.own rfl))) ?_
    refine .let_ (live := true) rfl (.write (.read (.own rfl)) (.deref (.own rfl))) ?_
    refine .let_ (live := false) rfl (.inj (.move rfl rfl) rfl) ?_
    exact .let_ (live := true) rfl (.perform (op := chMsg) rfl (by simp) (.cons (.move rfl rfl) .nil) .nil .nil)
      (.write .lit (.own rfl))

theorem adder_ok : FnsOk [adder] chOps := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  refine ⟨by decide, ?_⟩
  simp only [adder, FnOk, fnCtx, cloFn, ownCtx, refCtx]
  refine ⟨by decide, [("p", .own .int true), ("z", .own .int true)], ?_⟩
  exact .let_ (live := true) rfl (.atom .lit)
    (.let_ (live := true) rfl (.while_ (.atom (.read (.own rfl))) lockStep_typed) (.atom .lit))

theorem mxArm_typed : Typed F O (armCtx ["m"] [] chMsg [("st", .mut, boxes)]) mxArm chRetT
    [("m", .own chMsgT false), ("st", .ref .mut boxes)] r :=
  .case (Γ₁ := [("m", .own chMsgT false), ("st", .ref .mut boxes)]) (Γ₂ := [("m", .own chMsgT false), ("st", .ref .mut boxes)])
    (l₁ := false) (l₂ := true) rfl rfl rfl
    (.let_ (live := true) rfl (.vpush (.move rfl rfl) (.ref (m := .mut) rfl)) (.inj .lit rfl))
    (.vpop (.ref (m := .mut) rfl) rfl) (Weaker.refl _) (Weaker.refl _)

def mxH : Ctx := [("u0", .own .int true), ("b0", .own (.box .int) false), ("st", .lent boxes false)]

theorem mutexEx_typed : Typed [adder] chOps [] mutexEx .int [] [.fail] := by
  refine .let_ (live := true) rfl (.vnew rfl) ?_
  refine .let_ (live := false) rfl (.new .lit) ?_
  refine .let_ (live := true) rfl (.vpush (.move rfl rfl) (.own rfl)) ?_
  have hs : Typed [adder] chOps mxH
      (.scope 0 1 [] .int
        (.let_ "k" (.fn .once .int .int [.eff 0, .eff 2] .nil) (.lam 0 (.lit 20))
          (.let_ "s1" .int (.perform 1 [.move "k"] [])
            (.let_ "k2" (.fn .once .int .int [.eff 0, .eff 2] .nil) (.lam 0 (.lit 22))
              (.let_ "s2" .int (.perform 1 [.move "k2"] []) (yield_ "y" (.atom (.lit 0))))))))
      .int mxH [.eff 2, .fail] := by
    refine .scope (op := scYield) (opS := chSpawn) (rT := [.eff 0, .eff 2]) rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
      (by simp) (by simp) (by decide) rfl (by simp) ?_
    refine .let_ (live := false) rfl (.lam (d := adder) rfl rfl rfl rfl rfl .lit rfl) ?_
    refine .let_ (live := true) rfl (.perform (op := chSpawn) rfl (by simp) (.cons (.move rfl rfl) .nil) .nil .nil) ?_
    refine .let_ (live := false) rfl (.lam (d := adder) rfl rfl rfl rfl rfl .lit rfl) ?_
    refine .let_ (live := true) rfl (.perform (op := chSpawn) rfl (by simp) (.cons (.move rfl rfl) .nil) .nil .nil) ?_
    exact .let_ (live := true) rfl (.perform (op := scYield) rfl (by simp) .nil .nil .nil) (.atom .lit)
  have hh := Typed.handle (F := [adder]) (O := chOps)
    (Γ := [("u0", .own .int true), ("b0", .own (.box .int) false), ("st", .own boxes true)]) (e := 2)
    (op := chMsg) (os := ["m"]) (rs := []) (caps := [⟨"st", .mut, boxes, var "st"⟩])
    (ys := [(.mut, "st")]) (r := [.fail]) (Γb := mxH) (τ := .int) (arm := mxArm) (body := .scope 0 1 [] .int
        (.let_ "k" (.fn .once .int .int [.eff 0, .eff 2] .nil) (.lam 0 (.lit 20))
          (.let_ "s1" .int (.perform 1 [.move "k"] [])
            (.let_ "k2" (.fn .once .int .int [.eff 0, .eff 2] .nil) (.lam 0 (.lit 22))
              (.let_ "s2" .int (.perform 1 [.move "k2"] []) (yield_ "y" (.atom (.lit 0))))))))
    rfl rfl (by simp [chMsg, chMsgT]; rfl) rfl rfl (.mut (.own rfl) rfl rfl .nil)
    (by simp [Exclusive]) (by decide) mxArm_typed hs
  simp only [thaw, unhideAll, hideAll, hide, roots, Slot.ty, mxH] at hh
  refine .let_ (live := true) rfl hh ?_
  refine .let_ (live := false) rfl (.vpop (.own rfl) rfl) ?_
  let C : Ctx := [("r", .own chRetT false), ("h", .own .int true), ("u0", .own .int true), ("b0", .own (.box .int) false),
    ("st", .own boxes true)]
  exact .case (Γ₁ := C) (Γ₂ := C) (l₁ := true) (l₂ := true) rfl rfl rfl (.atom .lit) (.atom (.read (.deref (.own rfl))))
    (Weaker.refl _) (Weaker.refl _)

/-- Under any schedule. -/
theorem mutexEx_ok (s p : Nat → Bool) : ∀ n, match eval [adder] chOps n [.abort .fail 0] (Store.sched0 s p) [] mutexEx with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT [adder] ⟨[], Wstar [adder] chOps⟩ σ' .int v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok_sched adder_ok mutexEx_typed s p

end FlyCore.Ownership.Concurrency
