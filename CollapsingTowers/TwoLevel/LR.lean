
import Mathlib.Data.Finset.Basic
import CollapsingTowers.TwoLevel.Basic
import CollapsingTowers.TwoLevel.OpenClose
import CollapsingTowers.TwoLevel.SmallStep
import CollapsingTowers.TwoLevel.Env
import CollapsingTowers.TwoLevel.Typing

@[simp]
def valType : Expr → Ty → Prop
  | .lam₁ t2, .arrow τ1 τ2 =>
    ∀ v1, valType v1 τ1 ∧ lc v1 →
    ∃ v2, stepn (openSubst v1 t2) v2 ∧ valType v2 τ2
  | .lit₁ _, .nat => true
  | .code e, .rep τ =>
    ∃ v, stepn e v ∧ valType v τ
  | _, _ => false

@[simp]
def expType (e : Expr) (τ : Ty) : Prop :=
  ∃ v, stepn e v ∧ lc v ∧ valType v τ

@[simp]
def envType (Δ : VEnv) (Γ : TEnv) : Prop :=
  Δ.length = Γ.length ∧ ∀ τ x, binds x τ Γ → ∃ v, indexr x Δ = some v ∧ lc v ∧ valType v τ

theorem envTypeMt : envType [] [] := by simp

theorem envTypeExtend : ∀ Δ Γ v τ,
  envType Δ Γ → lc v → valType v τ → envType (v :: Δ) (τ :: Γ) :=
  by
  intros Δ Γ v τ henv hcl hv; simp; simp at henv
  apply And.intro
  . apply henv.1
  . intros τ1 x bd; rcases henv with ⟨hlen, h⟩
    by_cases hx : (x = Γ.length)
    . rw [hx] at bd; simp at bd; rw [hlen]; simp [hx]; rw [<- bd]; apply And.intro; assumption; assumption
    . rw [if_neg hx] at bd; rw [hlen]; rw [if_neg hx]
      apply h; assumption

theorem envTypeClosed : ∀ Δ Γ,
  envType Δ Γ → (∀ x t1, indexr x Δ = some t1 → lc t1) := by sorry

@[simp]
def substF (Δ : VEnv) (t : Expr) : Expr :=
  match t with
  | .bvar _ => t
  | .fvar x =>
    match indexr x Δ with
    | none => t
    | some t' => t'
  | .lam₁ t1 => .lam₁ (substF Δ t1)
  | .lam₂ t1 => .lam₂ (substF Δ t1)
  | .app₁ t11 t12 => .app₁ (substF Δ t11) (substF Δ t12)
  | .app₂ t11 t12 => .app₂ (substF Δ t11) (substF Δ t12)
  | .lit₁ _ => t
  | .lit₂ _ => t
  | .plus₁ t1 t2 => .plus₁ (substF Δ t1) (substF Δ t2)
  | .plus₂ t1 t2 => .plus₂ (substF Δ t1) (substF Δ t2)
  | .code t1 => .code (substF Δ t1)
  | .reflect t1 => .reflect (substF Δ t1)
  | .lam𝕔 t1 => .lam𝕔 (substF Δ t1)
  | .lets t1 t2 => .lets (substF Δ t1) (substF Δ t2)
  | .let𝕔 t1 t2 => .let𝕔 (substF Δ t1) (substF Δ t2)

@[simp]
def semType (Γ : TEnv) (t : Expr) (τ : Ty) : Prop :=
  ∀ Δ, lc t → envType Δ Γ → expType (substF Δ t) τ
