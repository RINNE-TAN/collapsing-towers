import CollapsingTowers.TwoLevelMut.Syntax.Defs
import CollapsingTowers.TwoLevelMut.SyntacticTyping.Env
import CollapsingTowers.TwoLevelMut.OperationalSemantics.Defs

mutual
  inductive typing : TEnv → Stage → Expr → Ty → Effect → Bool → Prop where
    | fvar : ∀ Γ 𝕊 x τ,
      binds x (τ, 𝕊) Γ →
      wbt 𝕊 τ →
      typing Γ 𝕊 (.fvar x) τ ⊥ ⊥
    | lam : ∀ Γ 𝕊 e τ𝕒 τ𝕓 φ ω,
      typing ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ ω →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.lam e) (.arrow τ𝕒 τ𝕓 φ) ⊥ ω
    | lift_lam : ∀ Γ e τ𝕒 τ𝕓 φ₀ φ₁ ω,
      typing Γ 𝟙 e (.arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀) φ₁ ω →
      typing Γ 𝟙 (.lift e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤ ω
    | app₁ : ∀ Γ 𝕊 f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂ ω₁ ω₂,
      typing Γ 𝕊 f (.arrow τ𝕒 τ𝕓 φ₀) φ₁ ω₁ →
      typing Γ 𝕊 arg τ𝕒 φ₂ ω₂ →
      typing Γ 𝕊 (.app₁ f arg) τ𝕓 (φ₀ ∪ φ₁ ∪ φ₂) (ω₁ ∨ ω₂)
    | app₂ : ∀ Γ f arg τ𝕒 τ𝕓 φ₁ φ₂ ω₁ ω₂,
      typing Γ 𝟙 f (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) φ₁ ω₁ →
      typing Γ 𝟙 arg (.fragment τ𝕒) φ₂ ω₂ →
      typing Γ 𝟙 (.app₂ f arg) (.fragment τ𝕓) ⊤ (ω₁ ∨ ω₂)
    | lit : ∀ Γ 𝕊 n,
      typing Γ 𝕊 (.lit n) .nat ⊥ ⊥
    | lift_lit : ∀ Γ n φ ω,
      typing Γ 𝟙 n .nat φ ω →
      typing Γ 𝟙 (.lift n) (.fragment .nat) ⊤ ω
    | code_fragment : ∀ Γ x τ,
      binds x (τ, 𝟚) Γ →
      wbt 𝟚 τ →
      typing Γ 𝟙 (.code (.fvar x)) (.fragment τ) ⊥ ⊥
    | code_rep : ∀ Γ e τ ω,
      typing Γ 𝟚 e τ ⊥ ω →
      typing Γ 𝟙 (.code e) (.rep τ) ⊥ ω
    | reflect : ∀ Γ e τ ω,
      typing Γ 𝟚 e τ ⊥ ω →
      typing Γ 𝟙 (.reflect e) (.fragment τ) ⊤ ω
    | lam𝕔 : ∀ Γ e τ𝕒 τ𝕓 φ ω,
      typing_reification ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ ω →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝟙 (.lam𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤ ω
    | lets : ∀ Γ 𝕊 b e τ𝕒 τ𝕓 φ₀ φ₁ ω₀ ω₁,
      typing Γ 𝕊 b τ𝕒 φ₀ ω₀ →
      typing ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ₁ ω₁ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.lets b e) τ𝕓 (φ₀ ∪ φ₁) (ω₀ ∨ ω₁)
    | lets𝕔 : ∀ Γ b e τ𝕒 τ𝕓 φ₁ ω₀ ω₁,
      typing Γ 𝟚 b τ𝕒 ⊥ ω₀ →
      typing_reification ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ₁ ω₁ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝟙 (.lets𝕔 b e) (.rep τ𝕓) ⊥ (ω₀ ∨ ω₁)
    | run : ∀ Γ e τ φ,
      typing_reification Γ e (.rep τ) φ ⊥ →
      closed e →
      typing Γ 𝟙 (.run e) τ ⊥ ⊥
    | unit : ∀ Γ 𝕊,
      typing Γ 𝕊 .unit .unit ⊥ ⊥
    | lift_unit : ∀ Γ e φ ω,
      typing Γ 𝟙 e .unit φ ω →
      typing Γ 𝟙 (.lift e) (.fragment .unit) ⊤ ω
    | alloc₁ : ∀ Γ e φ ω,
      typing Γ 𝟚 e .nat φ ω →
      typing Γ 𝟚 (.alloc₁ e) (.ref .nat) φ ⊤
    | alloc₂ : ∀ Γ e φ ω,
      typing Γ 𝟙 e (.fragment .nat) φ ω →
      typing Γ 𝟙 (.alloc₂ e) (.fragment (.ref .nat)) ⊤ ⊤
    | load₁ : ∀ Γ e φ ω,
      typing Γ 𝟚 e (.ref .nat) φ ω →
      typing Γ 𝟚 (.load₁ e) .nat φ ⊤
    | load₂ : ∀ Γ e φ ω,
      typing Γ 𝟙 e (.fragment (.ref .nat)) φ ω →
      typing Γ 𝟙 (.load₂ e) (.fragment .nat) ⊤ ⊤
    | store₁ : ∀ Γ l r φ₀ φ₁ ω₀ ω₁,
      typing Γ 𝟚 l (.ref .nat) φ₀ ω₀ →
      typing Γ 𝟚 r .nat φ₁ ω₁ →
      typing Γ 𝟚 (.store₁ l r) .unit (φ₀ ∪ φ₁) ⊤
    | store₂ : ∀ Γ l r φ₀ φ₁ ω₀ ω₁,
      typing Γ 𝟙 l (.fragment (.ref .nat)) φ₀ ω₀ →
      typing Γ 𝟙 r (.fragment .nat) φ₁ ω₁ →
      typing Γ 𝟙 (.store₂ l r) (.fragment .unit) ⊤ ⊤

  inductive typing_reification : TEnv → Expr → Ty → Effect → Bool → Prop
    | pure : ∀ Γ e τ ω, typing Γ 𝟙 e τ ⊥ ω → typing_reification Γ e τ ⊥ ω
    | reify : ∀ Γ e τ φ ω, typing Γ 𝟙 e (.fragment τ) φ ω → typing_reification Γ e (.rep τ) φ ω
end
