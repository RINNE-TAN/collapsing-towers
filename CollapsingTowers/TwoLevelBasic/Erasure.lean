
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
def erase_ty : Ty → Ty
  | .nat => .nat
  | .arrow τa τb _ => .arrow (erase_ty τa) (erase_ty τb) ∅
  | .fragment τ => erase_ty τ
  | .rep τ => erase_ty τ

@[simp]
def erase_env : TEnv → TEnv
  | [] => []
  | (τ, _) :: Γ => (erase_ty τ, .stat) :: erase_env Γ

theorem erase_lc_at : ∀ e i, lc_at e i → lc_at (erase e) i :=
  by
  intros e i Hclose
  induction e generalizing i with
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

theorem erase_opening_comm : ∀ i v e, erase (opening i v e) = opening i (erase v) (erase e) :=
  by
  intros i v e
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

theorem erase_open_subst_comm : ∀ v e, erase (open_subst v e) = open_subst (erase v) (erase e) :=
  by
  intros v e; apply erase_opening_comm

theorem erase_maping𝕔 : ∀ i e, erase (maping𝕔 e i) = erase e :=
  by
  intros i e
  induction e generalizing i with
  | bvar j => by_cases HEq : j = i; rw [HEq]; simp; simp [if_neg HEq]
  | fvar y => simp
  | lam _ IH
  | lift _ IH
  | code _ IH
  | reflect _ IH
  | lam𝕔 _ IH
  | run _ IH =>
    simp; apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | let𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply IH₁
  | lit => simp

theorem erase_ty_well_binding_time : ∀ 𝕊 τ, well_binding_time 𝕊 (erase_ty τ) :=
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

theorem length_erase_env : ∀ Γ, Γ.length = (erase_env Γ).length :=
  by
  intros Γ
  induction Γ
  case nil => rfl
  case cons IH => simp; apply IH

theorem binds_erase_env : ∀ x τ 𝕊 Γ, binds x (τ, 𝕊) Γ → binds x ((erase_ty τ), .stat) (erase_env Γ) :=
  by
  intros x τ 𝕊 Γ Hbinds
  induction Γ
  case nil => nomatch Hbinds
  case cons tails IH =>
    by_cases HEq : tails.length = x
    . simp [if_pos HEq] at Hbinds
      simp [← length_erase_env, if_pos HEq, Hbinds]
    . simp [if_neg HEq] at Hbinds
      simp [← length_erase_env, if_neg HEq]
      apply IH; apply Hbinds

-- Γ ⊢ e₀ : τ
-- ————————————————
-- |Γ| ⊢ |e₀| : |τ|
theorem erase_safety : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → typing (erase_env Γ) .stat (erase e) (erase_ty τ) ∅ :=
  by
  intros Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => typing (erase_env Γ) .stat (erase e) (erase_ty τ) ∅)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) => typing (erase_env Γ) .stat (erase e) (erase_ty τ) ∅)
  case fvar =>
    intros _ _ _ _ Hbinds _
    apply typing.fvar
    apply binds_erase_env; apply Hbinds
    apply erase_ty_well_binding_time
  case lam =>
    intros _ _ _ _ _ _ _ HwellBinds Hclose IH
    apply typing.lam
    rw [← length_erase_env, ← erase_open₀_comm]
    apply IH
    apply erase_ty_well_binding_time
    rw [← length_erase_env]
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
    simp; apply binds_erase_env; apply Hbinds
    apply erase_ty_well_binding_time
  case code_rep =>
    intros _ _ _ _ IH
    apply IH
  case reflect =>
    intros _ _ _ _ IH
    apply IH
  case lam𝕔 =>
    intros _ _ _ _ _ _ _ Hclose IH
    apply typing.lam
    rw [← length_erase_env, ← erase_open₀_comm]
    apply IH
    apply erase_ty_well_binding_time
    rw [← length_erase_env]
    apply erase_closed_at; apply Hclose
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ Hclose IHb IHe
    rw [← union_pure_left ∅]
    apply typing.lets
    apply IHb
    rw [← length_erase_env, ← erase_open₀_comm]
    apply IHe
    apply erase_ty_well_binding_time
    rw [← length_erase_env]
    apply erase_closed_at; apply Hclose
  case let𝕔 =>
    intros _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe
    rw [← union_pure_left ∅]
    apply typing.lets
    apply IHb
    rw [← length_erase_env, ← erase_open₀_comm]
    apply IHe
    apply erase_ty_well_binding_time
    rw [← length_erase_env]
    apply erase_closed_at; apply Hclose
  case run =>
    intros _ _ _ _ _ _ IH
    apply IH
  case pure =>
    intros _ _ _ _ IH
    apply IH
  case reify =>
    intros _ _ _ _ _ IH
    apply IH
  apply Hτ

theorem erase_reification_safety : ∀ Γ e τ φ, typing_reification Γ e τ φ → typing_reification (erase_env Γ) (erase e) (erase_ty τ) ∅ :=
  by
  intros Γ e τ φ Hτ
  cases Hτ <;>
  next Hτ =>
    apply typing_reification.pure
    apply erase_safety _ _ _ _ _ Hτ
