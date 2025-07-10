
import CollapsingTowers.TwoLevelBasic.Typing
@[simp]
def erase : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => .fvar y
  | .lam e => .lam (erase e)
  | .lift e => erase e
  | .app₁ f arg => .app₁ (erase f) (erase arg)
  | .app₂ f arg => .app₁ (erase f) (erase arg)
  | .lit n => .lit n
  | .run e => erase e
  | .code e => erase e
  | .reflect e => erase e
  | .lam𝕔 e => .lam (erase e)
  | .lets b e => .lets (erase b) (erase e)
  | .let𝕔 b e => .lets (erase b) (erase e)

@[simp]
def eraseTy : Ty → Ty
  | .nat => .nat
  | .arrow τa τb _ => .arrow (eraseTy τa) (eraseTy τb) ∅
  | .fragment τ => eraseTy τ
  | .rep τ => eraseTy τ

@[simp]
def eraseTEnv : TEnv → TEnv
  | [] => []
  | (τ, _) :: Γ => (eraseTy τ, .stat) :: eraseTEnv Γ

theorem erase_closed_at : ∀ e x, closed_at e x → closed_at (erase e) x :=
  by
  intros e x Hclose
  induction e with
  | fvar| lit| bvar => assumption
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hclose.left
    apply IH₁; apply Hclose.right
  | code _ IH
  | reflect _ IH
  | lift _ IH
  | run _ IH
  | lam _ IH
  | lam𝕔 _ IH =>
    apply IH; apply Hclose

theorem erase_opening_comm : ∀ i x e, erase (opening i (.fvar x) e) = opening i (.fvar x) (erase e) :=
  by
  intros i x e
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]
    . simp [if_neg HEq]
  | fvar| lit => simp
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply IH₁
  | code _ IH
  | reflect _ IH
  | lift _ IH
  | run _ IH
  | lam _ IH
  | lam𝕔 _ IH => simp; apply IH

theorem erase_open₀_comm : ∀ x e, erase (open₀ x e) = open₀ x (erase e) :=
  by
  intros x e; apply erase_opening_comm

theorem eraseTy_well_binding_time : ∀ 𝕊 τ, well_binding_time 𝕊 (eraseTy τ) :=
  by
  intros 𝕊 τ
  induction τ
  case nat => cases 𝕊 <;> simp
  case arrow IH₀ IH₁ =>
    cases 𝕊
    case stat =>
      constructor; apply IH₀; apply IH₁
    case dyn =>
      constructor; rfl
      constructor; apply IH₀; apply IH₁
  case fragment IH => apply IH
  case rep IH => apply IH

theorem length_eraseTEnv : ∀ Γ, Γ.length = (eraseTEnv Γ).length :=
  by
  intros Γ
  induction Γ
  case nil => rfl
  case cons IH => simp; apply IH

theorem erase_safety : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → typing (eraseTEnv Γ) .stat (erase e) (eraseTy τ) ∅ :=
  by
  intros Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => typing (eraseTEnv Γ) .stat (erase e) (eraseTy τ) ∅)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) => typing_reification (eraseTEnv Γ) (erase e) (eraseTy τ) ∅)
  case fvar =>
    intros _ _ _ _ Hbinds _
    apply typing.fvar
    admit
    apply eraseTy_well_binding_time
  case lam =>
    intros _ _ _ _ _ _ _ HwellBinds Hclose IH
    apply typing.lam
    rw [← length_eraseTEnv, ← erase_open₀_comm]
    apply IH
    apply eraseTy_well_binding_time
    rw [← length_eraseTEnv]
    apply erase_closed_at; apply Hclose
  case lift_lam =>
    intros _ _ _ _ _ _ _ IH
    apply IH
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ IHf IHarg
    rw [← union_pure_left ∅, ← union_pure_left ∅]
    apply typing.app₁
    apply IHf; apply IHarg
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ IHf IHarg
    rw [← union_pure_left ∅, ← union_pure_left ∅]
    apply typing.app₁
    apply IHf; apply IHarg
  case lit =>
    intros _ _ _
    apply typing.lit
  case lift_lit =>
    intros _ _ _ _ IH
    apply IH
  case code_fragment =>
    intros _ x _ Hbinds HwellBinds
    apply typing.fvar
    admit
    apply eraseTy_well_binding_time
  case code_rep =>
    intros _ _ _ _ IH
    apply IH
  case reflect =>
    intros _ _ _ _ IH
    apply IH
  case lam𝕔 =>
    intros _ _ _ _ _ _ _ _ IH
    apply typing.lam
    all_goals admit
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ Hclose IHb IHe
    rw [← union_pure_left ∅]
    apply typing.lets
    apply IHb
    rw [← length_eraseTEnv, ← erase_open₀_comm]
    apply IHe
    apply eraseTy_well_binding_time
    rw [← length_eraseTEnv]
    apply erase_closed_at; apply Hclose
  case let𝕔 =>
    intros _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe
    rw [← union_pure_left ∅]
    apply typing.lets
    apply IHb
    rw [← length_eraseTEnv, ← erase_open₀_comm]
    all_goals admit
  case run =>
    intros _ _ _ _ _ Hclose IH
    all_goals admit
  case pure =>
    intros _ _ _ _ IH
    apply typing_reification.pure
    apply IH
  case reify =>
    intros _ _ _ _ _ IH
    apply typing_reification.pure
    apply IH
  apply Hτ
