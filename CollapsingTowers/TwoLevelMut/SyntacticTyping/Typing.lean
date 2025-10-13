import CollapsingTowers.TwoLevelMut.Syntax.Defs
import CollapsingTowers.TwoLevelMut.SyntacticTyping.Env
import CollapsingTowers.TwoLevelMut.OperationalSemantics.Defs

mutual
  inductive typing : Store → TEnv → Stage → Expr → Ty → Effect → Prop where
    | fvar : ∀ σ Γ 𝕊 x τ,
      binds x (τ, 𝕊) Γ →
      wbt 𝕊 τ →
      typing σ Γ 𝕊 (.fvar x) τ ⊥
    | lam : ∀ σ Γ 𝕊 e τ𝕒 τ𝕓 φ,
      typing σ ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing σ Γ 𝕊 (.lam e) (.arrow τ𝕒 τ𝕓 φ) ⊥
    | lift_lam : ∀ σ Γ e τ𝕒 τ𝕓 φ₀ φ₁,
      typing σ Γ 𝟙 e (.arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀) φ₁ →
      typing σ Γ 𝟙 (.lift e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤
    | app₁ : ∀ σ Γ 𝕊 f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂,
      typing σ Γ 𝕊 f (.arrow τ𝕒 τ𝕓 φ₀) φ₁ →
      typing σ Γ 𝕊 arg τ𝕒 φ₂ →
      typing σ Γ 𝕊 (.app₁ f arg) τ𝕓 (φ₀ ∪ φ₁ ∪ φ₂)
    | app₂ : ∀ σ Γ f arg τ𝕒 τ𝕓 φ₀ φ₁,
      typing σ Γ 𝟙 f (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) φ₀ →
      typing σ Γ 𝟙 arg (.fragment τ𝕒) φ₁ →
      typing σ Γ 𝟙 (.app₂ f arg) (.fragment τ𝕓) ⊤
    | lit : ∀ σ Γ 𝕊 n,
      typing σ Γ 𝕊 (.lit n) .nat ⊥
    | lift_lit : ∀ σ Γ n φ,
      typing σ Γ 𝟙 n .nat φ →
      typing σ Γ 𝟙 (.lift n) (.fragment .nat) ⊤
    | code_fragment : ∀ σ Γ x τ,
      binds x (τ, 𝟚) Γ →
      wbt 𝟚 τ →
      typing σ Γ 𝟙 (.code (.fvar x)) (.fragment τ) ⊥
    | code_rep : ∀ σ Γ e τ,
      typing σ Γ 𝟚 e τ ⊥ →
      typing σ Γ 𝟙 (.code e) (.rep τ) ⊥
    | reflect : ∀ σ Γ e τ,
      typing σ Γ 𝟚 e τ ⊥ →
      typing σ Γ 𝟙 (.reflect e) (.fragment τ) ⊤
    | lam𝕔 : ∀ σ Γ e τ𝕒 τ𝕓 φ,
      typing_reification σ ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing σ Γ 𝟙 (.lam𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤
    | lets : ∀ σ Γ 𝕊 b e τ𝕒 τ𝕓 φ₀ φ₁,
      typing σ Γ 𝕊 b τ𝕒 φ₀ →
      typing σ ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ₁ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing σ Γ 𝕊 (.lets b e) τ𝕓 (φ₀ ∪ φ₁)
    | lets𝕔 : ∀ σ Γ b e τ𝕒 τ𝕓 φ,
      typing σ Γ 𝟚 b τ𝕒 ⊥ →
      typing_reification σ ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing σ Γ 𝟙 (.lets𝕔 b e) (.rep τ𝕓) ⊥
    | run : ∀ σ Γ e τ φ,
      typing_reification σ Γ e (.rep τ) φ →
      closed e →
      typing σ Γ 𝟙 (.run e) τ ⊥
    | unit : ∀ σ Γ 𝕊,
      typing σ Γ 𝕊 .unit .unit ⊥
    | loc : ∀ σ Γ l,
      l < σ.length →
      typing σ Γ 𝟙 (.loc l) (.ref .nat) ⊥
    | alloc₁ : ∀ σ Γ 𝕊 e φ,
      typing σ Γ 𝕊 e .nat φ →
      typing σ Γ 𝕊 (.alloc₁ e) (.ref .nat) φ
    | alloc₂ : ∀ σ Γ e φ,
      typing σ Γ 𝟙 e (.fragment .nat) φ →
      typing σ Γ 𝟙 (.alloc₂ e) (.fragment (.ref .nat)) ⊤
    | load₁ : ∀ σ Γ 𝕊 e φ,
      typing σ Γ 𝕊 e (.ref .nat) φ →
      typing σ Γ 𝕊 (.load₁ e) .nat φ
    | load₂ : ∀ σ Γ e φ,
      typing σ Γ 𝟙 e (.fragment (.ref .nat)) φ →
      typing σ Γ 𝟙 (.load₂ e) (.fragment .nat) ⊤
    | store₁ : ∀ σ Γ 𝕊 l r φ₀ φ₁,
      typing σ Γ 𝕊 l (.ref .nat) φ₀ →
      typing σ Γ 𝕊 r .nat φ₁ →
      typing σ Γ 𝕊 (.store₁ l r) .unit (φ₀ ∪ φ₁)
    | store₂ : ∀ σ Γ l r φ₀ φ₁,
      typing σ Γ 𝟙 l (.fragment (.ref .nat)) φ₀ →
      typing σ Γ 𝟙 r (.fragment .nat) φ₁ →
      typing σ Γ 𝟙 (.store₂ l r) (.fragment .unit) ⊤

  inductive typing_reification : Store → TEnv → Expr → Ty → Effect → Prop
    | pure : ∀ σ Γ e τ, typing σ Γ 𝟙 e τ ⊥ → typing_reification σ Γ e τ ⊥
    | reify : ∀ σ Γ e τ φ, typing σ Γ 𝟙 e (.fragment τ) φ → typing_reification σ Γ e (.rep τ) φ
end
