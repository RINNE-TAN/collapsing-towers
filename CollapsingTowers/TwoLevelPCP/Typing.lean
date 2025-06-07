
import CollapsingTowers.TwoLevelPCP.Syntax
import CollapsingTowers.TwoLevelPCP.SmallStep
import CollapsingTowers.TwoLevelPCP.Env
@[simp]
def well_binding_time : Stage → Ty → Prop
  | .stat, .nat => true
  | .stat, (.arrow τ𝕒 τ𝕓 _) => well_binding_time .stat τ𝕒 ∧ well_binding_time .stat τ𝕓
  | .stat, (.fragment τ) => well_binding_time .dyn τ
  | .stat, _ => false
  | .dyn, .nat => true
  | .dyn, (.arrow τ𝕒 τ𝕓 φ) => φ = ∅ ∧ well_binding_time .dyn τ𝕒 ∧ well_binding_time .dyn τ𝕓
  | .dyn, _ => false

mutual
  inductive typing : TEnv → Stage → Expr → Ty → Effects → Prop where
    | fvar : ∀ Γ 𝕊 x τ,
      binds x τ 𝕊 Γ →
      typing Γ 𝕊 (.fvar x) τ ∅
    | lam₁ : ∀ Γ 𝕊 e τ𝕒 τ𝕓 φ,
      typing ((τ𝕒, 𝕊) :: Γ) 𝕊 (open₀ Γ.length e) τ𝕓 φ →
      well_binding_time 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.lam₁ e) (.arrow τ𝕒 τ𝕓 φ) ∅
    | lift_lam : ∀ Γ e τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ .stat e (.arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀) φ₁ →
      typing Γ .stat (.lift e) (.fragment (.arrow τ𝕒 τ𝕓 ∅)) .reify
    | app₁ : ∀ Γ 𝕊 f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂,
      typing Γ 𝕊 f (.arrow τ𝕒 τ𝕓 φ₀) φ₁ →
      typing Γ 𝕊 arg τ𝕒 φ₂ →
      typing Γ 𝕊 (.app₁ f arg) τ𝕓 (φ₀ ∪ φ₁ ∪ φ₂)
    | app₂ : ∀ Γ f arg τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ .stat f (.fragment (.arrow τ𝕒 τ𝕓 ∅)) φ₀ →
      typing Γ .stat arg (.fragment τ𝕒) φ₁ →
      typing Γ .stat (.app₂ f arg) (.fragment τ𝕓) .reify
    | plus₁ : ∀ Γ 𝕊 l r φ₀ φ₁,
      typing Γ 𝕊 l .nat φ₀ →
      typing Γ 𝕊 r .nat φ₁ →
      typing Γ 𝕊 (.plus₁ l r) .nat (φ₀ ∪ φ₁)
    | plus₂ : ∀ Γ l r φ₀ φ₁,
      typing Γ .stat l (.fragment .nat) φ₀ →
      typing Γ .stat r (.fragment .nat) φ₁ →
      typing Γ .stat (.plus₂ l r) (.fragment .nat) .reify
    | lit₁ : ∀ Γ 𝕊 n,
      typing Γ 𝕊 (.lit₁ n) .nat ∅
    | lift_lit : ∀ Γ n φ,
      typing Γ .stat n .nat φ →
      typing Γ .stat (.lift n) (.fragment .nat) φ
    | code₁ : ∀ Γ x τ,
      binds x τ .dyn Γ →
      typing Γ .stat (.code (.fvar x)) (.fragment τ) ∅
    | code₂ : ∀ Γ e τ,
      typing Γ .dyn e τ ∅ →
      typing Γ .stat (.code e) (.rep τ) ∅
    | reflect : ∀ Γ e τ,
      typing Γ .dyn e τ ∅ →
      typing Γ .stat (.reflect e) (.fragment τ) .reify
    | lam𝕔 : ∀ Γ e τ𝕒 τ𝕓 φ,
      typing_reification ((τ𝕒, .dyn) :: Γ) (open₀ Γ.length e) (.rep τ𝕓) φ →
      well_binding_time .dyn τ𝕒 →
      closed_at e Γ.length →
      typing Γ .stat (.lam𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓 ∅)) .reify
    | lets : ∀ Γ 𝕊 b e τ𝕒 τ𝕓 φ₀ φ₁,
      typing Γ 𝕊 b τ𝕒 φ₀ →
      typing ((τ𝕒, 𝕊) :: Γ) 𝕊 (open₀ Γ.length e) τ𝕓 φ₁ →
      well_binding_time 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.lets b e) τ𝕓 (φ₀ ∪ φ₁)
    | let𝕔 : ∀ Γ b e τ𝕒 τ𝕓 φ,
      typing Γ .dyn b τ𝕒 ∅ →
      typing_reification ((τ𝕒, .dyn) :: Γ) (open₀ Γ.length e) (.rep τ𝕓) φ →
      well_binding_time .dyn τ𝕒 →
      closed_at e Γ.length →
      typing Γ .stat (.let𝕔 b e) (.rep τ𝕓) ∅

  inductive typing_reification : TEnv → Expr → Ty → Effects → Prop
    | pure : ∀ Γ e τ, typing Γ .stat e τ ∅ → typing_reification Γ e τ ∅
    | reify : ∀ Γ e τ, typing Γ .stat e (.fragment τ) .reify → typing_reification Γ e (.rep τ) .reify
end

theorem typing_regular : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → lc e :=
  by admit

theorem typing_closed : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → closed_at e Γ.length :=
  by admit

theorem typing_pure : ∀ Γ v τ φ, typing Γ .stat v τ φ → value v → φ = ∅ :=
  by
  intros _ _ _ _ Hτ Hvalue
  cases Hvalue <;> cases Hτ <;> rfl

theorem weakening : ∀ Γ Δ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → typing (Δ ++ Γ) 𝕊 e τ φ :=
  by admit
