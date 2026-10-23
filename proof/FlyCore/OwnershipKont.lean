import FlyCore.OwnershipCall

/-!
# Ownership: the code around what runs

What evaluation gives, and what the code around it is. A result is a value, an unwinding aimed at a
handler, or an operation performed with the code that performed it suspended, as frames — its
continuation — that the operation's handler resumes with its arm's value. Each frame is typed: it
takes what the code it ran gives, at a level — variables, where they are, a type, what is only read,
a row — and gives what the construct it belongs to does, at the level around; and it keeps cells of
its own, which nothing changes while it is suspended.
-/

namespace FlyCore.Ownership

/-- An unwinding is aimed at a handler in force. -/
def AimedIn (id : Nat) (hs : HS) : Prop := ∃ l, Frame.abort l id ∈ hs

/-- Every label of the row has a handler. -/
def Covers (hs : HS) (r : Row) : Prop := ∀ l ∈ r, ∃ f, find l hs = some f

/-- A handler stack whose frames are well formed: an unwinding one of an operation takes an integer
and lends nothing; one that resumes is for an operation the program has. -/
inductive HSOk (O : List Op) : HS → Prop
  | nil : HSOk O []
  | abort : (∀ e, l = .eff e → ∃ op, O[e]? = some op ∧ op.owns = [.int] ∧ op.refs = []) →
      HSOk O rest → HSOk O (.abort l hid :: rest)
  | capture : (∃ op, O[e]? = some op) → HSOk O rest → HSOk O (.capture e hid :: rest)

/-- Where code may run under `hs`, performing what `r` names: the handlers are well formed and handle
every label of the row. -/
def Ready (O : List Op) (hs : HS) (r : Row) : Prop := HSOk O hs ∧ Covers hs r

/-- What code at one level is: its variables, where they are, the type of what it gives, the cells
it only reads, and what it may perform. -/
structure Lvl where
  Γ : Ctx
  env : Env
  τ : Ty
  S : List Nat
  r : Row

/-- What an arm gives: what the code it took resumes with, or that and what it carries past the
resumption. -/
def armTy (op : Op) : PostR → Ty
  | none => op.ret
  | some (C, _) => .pair op.ret C

/-- What runs once the rest of a `handle` whose arm resumes in its midst ends: a function taking
what the arm carried and that value, and the places of the `handle`'s scope, lent to it again, its
value the `handle`'s. -/
def PostOk (F : List Fn) (O : List Op) (Γ : Ctx) (env : Env) (τ : Ty) (r : Row) : PostR → Prop
  | none => True
  | some (C, f, env', cps) => env' = env ∧ C.complete = true ∧ ∃ d ys, F[f]? = some d ∧
      d.owns.map Prod.snd = [C, τ] ∧ d.refs = cps.map Cap.sig ∧ d.retp = none ∧ d.cap = none ∧ d.ret = τ ∧
      (∀ l ∈ d.row, l ∈ r) ∧ Caps Γ cps ys ∧ Exclusive ys ∧
      ((d.owns.map Prod.fst) ++ (d.refs.map Prod.fst)).Nodup ∧ ∃ Γ'', Typed F O (fnCtx d) d.body d.ret Γ'' d.row

/-- What a `handle` whose arm resumes keeps while its body runs, its places resolved to `caps`: the
operation `op` it handles; an arm that takes the operation's arguments and the places and gives the
operation's result; and how the `handle`'s activation, `Γout`, is rebuilt from its body's, `Γin`, once
the body ends — with what it froze for the body, `Fz`, as it was, and with the trees the arm last left
at the places it was lent `mut`. `Rc` are the cells of the places lent `readonly`, which nothing
changes while the `handle` runs. -/
structure HandleOk (F : List Fn) (O : List Op) (σf : Store) (e : Nat) (caps : List (Cap Nat))
    (os rs : List Var) (arm : Expr) (post : PostR) (Γin Γout : Ctx) (env : Env) (Sin S : List Nat) (r : Row)
    (Fz Rc : List Nat) (op : Op) : Prop where
  hop : O[e]? = some op
  hcomp : ∀ τ ∈ op.owns, τ.complete = true
  hpref : post ≠ none → op.refs = []
  hown : os.length = op.owns.length
  href : rs.length = op.refs.length
  hnames : (os ++ rs ++ caps.map Cap.name).Nodup
  harm : ∃ Γa, Typed F O (armCtx os rs op (caps.map Cap.sig)) arm (armTy op post) Γa r
  hSin : ∀ l ∈ Sin, l ∈ Fz ∨ l ∈ S
  hS : ∀ l ∈ S, l ∈ Sin
  hRc : ∀ l ∈ Rc, l ∈ Fz ∨ l ∈ S
  hRcdet : ∀ σ1 Rc' Hc, Agree σf σ1 (Fz ++ S) → CapsOk F σ1 caps Rc' Hc → Rc' = Rc
  hfns : CapsFns caps
  hre : ∀ σ1 Eb Hc, Agree σf σ1 (Fz ++ S) → Disj (Fz ++ Hc) Eb → Disj S Hc → (Fz ++ Hc).Nodup →
    CapsOk F σ1 caps Rc Hc → Inv F σ1 Γin env Eb Sin →
    ∃ E', Inv F σ1 Γout env E' S ∧ ∀ z, z ∈ E' ↔ z ∈ Eb ∨ z ∈ Fz ∨ z ∈ Hc

/-- What a `handle` keeps holds wherever what it froze, and what its activation only reads, are as
they were. -/
theorem HandleOk.transfer (h : HandleOk F O σf e caps os rs arm post Γin Γout env Sin S r Fz Rc op)
    (hag : Agree σf σ' (Fz ++ S)) : HandleOk F O σ' e caps os rs arm post Γin Γout env Sin S r Fz Rc op :=
  { h with
    hRcdet := fun σ1 Rc' Hc hag' => h.hRcdet σ1 Rc' Hc fun l hl => (hag' l hl).trans (hag l hl)
    hre := fun σ1 Eb Hc hag' => h.hre σ1 Eb Hc fun l hl => (hag' l hl).trans (hag l hl) }

mutual
/-- `FrameOk σf f inL outL X A`: frame `f`, put in force where the store was `σf`, takes what the
code it ran gives at level `inL` and gives what its construct does at level `outL`; the cells `X` are
its own, as they were at `σf`; it may unwind to the handlers `A`. -/
inductive FrameOk (F : List Fn) (O : List Op) : Store → Kont → Lvl → Lvl → List Nat → List Nat → Prop
  | letK : lookup x Γ₁ = none → (Γ₁.map Prod.fst).Nodup →
      Typed F O ((x, .own τx true) :: Γ₁) b τb ((x, .own τx live) :: Γ₂) r →
      FrameOk F O σf (.letK x τx env b) ⟨Γ₁, env, τx, S, r⟩ ⟨Γ₂, env, τb, S, r⟩ [] []
  | scopeK : x ∉ Γ₂.map Prod.fst → (Γ₂.map Prod.fst).Nodup → τx.complete = true →
      FrameOk F O σf (.scopeK τx c) ⟨(x, .own τx live) :: Γ₂, (x, c) :: env, τ, S, r⟩ ⟨Γ₂, env, τ, S, r⟩ [] []
  | callK : (∀ l ∈ d.row, l ∈ r) → Inv F σf Γ₁ env E₁ S → (∀ h ∈ hos, HoleOk F σf Γ₁ env h) →
      hos.Pairwise Apart → hos.map (fun h => (h.mode, h.ty)) = d.refs.map Prod.snd →
      ((d.owns.map Prod.fst) ++ (d.refs.map Prod.fst)).Nodup → (∀ o ∈ d.owns, o.2.complete = true) →
      Typed F O (fnCtx d) d.body d.ret Γ'' d.row → cells.map Prod.fst = d.owns.map Prod.fst →
      FrameOk F O σf (.callK ((d.owns.map Prod.snd).zip (cells.map Prod.snd)))
        ⟨Γ'', cells ++ (d.refs.map Prod.fst).zip (hos.map Hole.loc), d.ret, roCells (olds hos), d.row⟩
        ⟨Γ₁, env, d.ret, S, r⟩ (E₁.filter (· ∉ mutCells (olds hos))) []
  /-- The body of a call that returns a borrow of its `i`th borrowed parameter's place `p`, which
the caller lent it as the hole `hd`: `body` runs with `x` the borrow, `hd`'s root only read, or not
reached, while it lives. -/
  | callLendK : (∀ l ∈ d.row, l ∈ r) → Inv F σf Γ₁ env E₁ S → (∀ h ∈ hos, HoleOk F σf Γ₁ env h) →
      hos.Pairwise Apart → hos.map (fun h => (h.mode, h.ty)) = d.refs.map Prod.snd →
      ((d.owns.map Prod.fst) ++ (d.refs.map Prod.fst)).Nodup → (∀ o ∈ d.owns, o.2.complete = true) →
      Typed F O (fnCtx d) d.body .int Γ'' d.row → cells.map Prod.fst = d.owns.map Prod.fst →
      (cs : List (Nat × Place)) ≠ [] →
      (∀ c ∈ cs, ∃ xi mi τi w hd, d.refs[c.1]? = some (xi, mi, τi) ∧ PlaceTy Γ'' c.2 d.ret w xi ∧
        (m = .mut → w = true) ∧ hos[c.1]? = some (hd : Hole) ∧ (m = .mut → hd.mode = .mut ∧ τi.isFn = false) ∧
        (m = .mut → ∀ s, lookup hd.root Γ₁ = some s → s.shell = true → hd.path = [])) →
      Pairs (fun c z => ∃ hd : Hole, hos[c.1]? = some hd ∧ hd.root = z) cs zs →
      (m = .mut → zs.Nodup ∧ d.ret.isFn = false) →
      (∀ z ∈ zs, ∀ τ', lookup z Γ₁ ≠ some (.own τ' false)) → lookup x Γ₁ = none →
      Typed F O ((x, .ref m d.ret) :: lendCtxs m Γ₁ zs) body τb ((x, .ref m d.ret) :: Γb) r →
      FrameOk F O σf (.callLendK x (cs.map Prod.snd) (cells ++ (d.refs.map Prod.fst).zip (hos.map Hole.loc))
          ((d.owns.map Prod.snd).zip (cells.map Prod.snd)) env body)
        ⟨Γ'', cells ++ (d.refs.map Prod.fst).zip (hos.map Hole.loc), .int, roCells (olds hos), d.row⟩
        ⟨unlend m Γ₁ zs Γb, env, τb, S, r⟩ (E₁.filter (· ∉ mutCells (olds hos))) []
  | catchK : lookup x Γb = none → (Γb.map Prod.fst).Nodup →
      Typed F O ((x, .own .int true) :: Γb) h τ ((x, .own .int live) :: Γh) r →
      (∀ e, l = .eff e → ∃ op, O[e]? = some op ∧ op.owns = [.int] ∧ op.refs = []) →
      FrameOk F O σf (.catchK l hid x env h) ⟨Γb, env, τ, S, l :: r⟩ ⟨Γh, env, τ, S, r⟩ [] []
  | whileC : Typed F O Γ c .int Γ r → Typed F O Γ b .int Γ r →
      FrameOk F O σf (.whileC env c b) ⟨Γ, env, .int, S, r⟩ ⟨Γ, env, .int, S, r⟩ [] []
  | whileB : Typed F O Γ c .int Γ r → Typed F O Γ b .int Γ r →
      FrameOk F O σf (.whileB env c b) ⟨Γ, env, .int, S, r⟩ ⟨Γ, env, .int, S, r⟩ [] []
  | deferK : Typed F O Γb d .int Γb r →
      FrameOk F O σf (.deferK τ env d) ⟨Γb, env, τ, S, r⟩ ⟨Γb, env, τ, S, r⟩ [] []
  | deferV : VT F σf τ v Lv →
      FrameOk F O σf (.deferV τ v) ⟨Γb, env, .int, S, r⟩ ⟨Γb, env, τ, S, r⟩ Lv []
  | deferA : FrameOk F O σf (.deferA hid k) ⟨Γb, env, .int, S, r⟩ ⟨Γb, env, τ, S, r⟩ [] [hid]
  | dropK : FrameOk F O σf (.dropK τ (.abort j k) d) ⟨Γ, env, τ, S, r⟩ ⟨Γ, env, τ', S, r⟩ [] [j]
  /-- A borrow held for a while: as it ends, the borrow's activation is the lender's again, with the
cells it kept from the borrow, `Xf`, as they were — what it froze, lent `readonly`, or the path to
the place, lent `mut`. -/
  | lendK : (∀ l ∈ Sin, l ∈ Xf ∨ l ∈ S) → (∀ l ∈ S, l ∈ Sin) →
      (∀ σ1 Eb, Agree σf σ1 (Xf ++ S) → Disj Xf Eb → Inv F σ1 Γin envin Eb Sin →
        ∃ E', Inv F σ1 Γout env E' S ∧ ∀ z, z ∈ E' ↔ z ∈ Eb ∨ z ∈ Xf) →
      FrameOk F O σf .lendK ⟨Γin, envin, τ, Sin, r⟩ ⟨Γout, env, τ, S, r⟩ Xf []
  /-- The code a closure over a `readonly` borrow is in scope for: as it ends, the closure's cell
`a`, one of the frame's own, is freed, and the activation is the lender's again. -/
  | cloK : (∀ l ∈ Sin, l ∈ Xf ∨ l ∈ S) → (∀ l ∈ S, l ∈ Sin) → a ∈ Xf →
      (∀ σ1 Eb, Agree σf σ1 (Xf ++ S) → Disj Xf Eb → Inv F σ1 Γin envin Eb Sin →
        ∃ E', Inv F σ1 Γout env E' S ∧ ∀ z, z ∈ E' ↔ z ∈ Eb ∨ (z ∈ Xf ∧ z ≠ a)) →
      FrameOk F O σf (.cloK a) ⟨Γin, envin, τ, Sin, r⟩ ⟨Γout, env, τ, S, r⟩ Xf []
  /-- The body of a `handle` whose arm resumes: its own cells are what it froze and the trees at
the places its arm was lent `mut`. -/
  | capK : HandleOk F O σf e caps os rs arm post Γin Γout env Sin S r Fz Rc op → PostOk F O Γout env τ r post →
      CapsOk F σf caps Rc Hc →
      FrameOk F O σf (.capK τ e hid caps os rs arm post) ⟨Γin, env, τ, Sin, .eff e :: r⟩ ⟨Γout, env, τ, S, r⟩
        (Fz ++ Hc) []
  /-- An arm running, the body of its `handle` suspended as `K`: its own cells are those of `K` and
what the `handle` froze. -/
  | armK : HandleOk F O σf e caps os rs arm post Γin Γout env Sin S r Fz Rc op → PostOk F O Γout env τ r post →
      FramesOk F O σf K op ⟨Γin, env, τ, Sin, .eff e :: r⟩ X hos AK →
      (∀ l ∈ roCells (olds hos), l ∈ X ∨ l ∈ Sin) →
      Typed F O (armCtx os rs op (caps.map Cap.sig)) arm (armTy op post) Γa r → cells.map Prod.fst = os →
      FrameOk F O σf (.armK τ (op.owns.zip (cells.map Prod.snd)) (.capK τ e hid caps os rs arm post :: K) post)
        ⟨Γa, cells ++ rs.zip (hos.map Hole.loc) ++ caps.map (fun c => (c.name, c.loc)), armTy op post,
          roCells (olds hos) ++ Rc, r⟩
        ⟨Γout, env, τ, S, r⟩ (X ++ Fz) AK
  /-- What an arm carried past its resumption, waiting for the rest of its `handle` to end: its cells
are the frame's own. -/
  | postR : PostOk F O Γ env τ r (some (C, f, env, cps)) → VT F σf C v Lv →
      FrameOk F O σf (.postR C f v env cps) ⟨Γ, env, τ, S, r⟩ ⟨Γ, env, τ, S, r⟩ Lv []

/-- `FramesOk σs K op top X hos A`: the frames `K`, the outermost first, suspended where the store is
`σs`, take the value of the operation `op` that suspended them and give what level `top` does;
their own cells are `X`; the code that performed the operation lent its handler the places `hos`;
and they may unwind to the handlers `A`. -/
inductive FramesOk (F : List Fn) (O : List Op) : Store → List Kont → Op → Lvl → List Nat → List Hole → List Nat → Prop
  | base : Inv F σs Γ₁ env E₁ S → (∀ h ∈ hos, HoleOk F σs Γ₁ env h) → hos.Pairwise Apart →
      O[e]? = some op → hos.map (fun h => (h.mode, h.ty)) = op.refs → Label.eff e ∈ r → Weaker Γ' Γ₁ →
      FramesOk F O σs [] op ⟨Γ', env, op.ret, S, r⟩ (E₁.filter (· ∉ mutCells (olds hos))) hos []
  | cons : FrameOk F O σf f mid ⟨Γ, env, τ, S, r⟩ Xf Af → Weaker Γ' Γ → Agree σf σs (Xf ++ S) →
      (∀ l ∈ Xf, σf.mem l ≠ none) → Xf.Nodup → Disj Xf (XK ++ mutCells (olds hos)) →
      FramesOk F O σs K op0 mid XK hos AK → (∀ a ∈ Af, a ∈ A) →
      (∀ a ∈ AK, a ∈ A ∨ AimedIn a (f.push [])) →
      FramesOk F O σs (f :: K) op0 ⟨Γ', env, τ, S, r⟩ (Xf ++ XK) hos A
end

/-- Continuations give what is said of a context weaker than the one their frames leave, where
branches meet. -/
theorem FramesOk.weaken (h : FramesOk F O σs K op0 ⟨Γ, env, τ, S, r⟩ X hos A) (w : Weaker Γ' Γ) :
    FramesOk F O σs K op0 ⟨Γ', env, τ, S, r⟩ X hos A := by
  cases h with
  | base hI hholes hpw hop hts hlab w' => exact .base hI hholes hpw hop hts hlab (w.trans w')
  | cons hf w' hag ha hn hd hK h1 h2 => exact .cons hf (w.trans w') hag ha hn hd hK h1 h2

/-- What evaluating under the handlers `hs` may give: never stuck; a value, with the activation
still well formed after, the value owning cells no variable does, and the step accounted for; an
unwinding aimed at one of the handlers, everything the scopes it left owned dropped, the activation
well formed as the expression would have left it; or an operation performed, the code that performed
it suspended as frames that give what the expression would, the operation's owned arguments and the
places it lends apart from them, the step accounted for. -/
def Post (F : List Fn) (O : List Op) (σ : Store) (E S : List Nat) (Γ' : Ctx) (env : Env) (τ : Ty)
    (r : Row) (hs : HS) : Res × Store → Prop
  | (.stuck, _) => False
  | (.timeout, _) => True
  | (.val v, σ') => ∃ E' L, Inv F σ' Γ' env E' S ∧ VT F σ' τ v L ∧ Disj L E' ∧ Disj L S ∧ Moves σ E σ' E' L
  | (.abort id _, σ') => AimedIn id hs ∧ ∃ E', Inv F σ' Γ' env E' S ∧ Moves σ E σ' E' []
  | (.susp id e vs ls K, σ') => ∃ op X hos A Lv,
      Frame.capture e id ∈ hs ∧ O[e]? = some op ∧ Covers hs r ∧ (∀ a ∈ A, AimedIn a hs) ∧
      FramesOk F O σ' K op ⟨Γ', env, τ, S, r⟩ X hos A ∧ ls = hos.map Hole.loc ∧
      Vals F σ' op.owns vs Lv ∧ Lv.flatten.Nodup ∧ Disj Lv.flatten (X ++ mutCells (olds hos)) ∧
      Disj Lv.flatten S ∧ Moves σ E σ' (X ++ mutCells (olds hos)) Lv.flatten

end FlyCore.Ownership
