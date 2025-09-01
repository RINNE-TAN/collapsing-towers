import CollapsingTowers.TwoLevelMut.Syntax.Defs
import CollapsingTowers.TwoLevelMut.SyntacticTyping.Env
import CollapsingTowers.TwoLevelMut.OperationalSemantics.Defs

mutual
  inductive typing : HEnv → TEnv → Stage → Expr → Ty → Effect → Prop where
    | fvar : ∀ Ω Γ 𝕊 x τ,
      binds x (τ, 𝕊) Γ →
      wbt 𝕊 τ →
      typing Ω Γ 𝕊 (.fvar x) τ ⊥
    | lam : ∀ Ω Γ 𝕊 e τ𝕒 τ𝕓 φ,
      typing Ω ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Ω Γ 𝕊 (.lam e) (.arrow τ𝕒 τ𝕓 φ) ⊥
    | lift_lam : ∀ Ω Γ e τ𝕒 τ𝕓 φ₀ φ₁,
      typing Ω Γ 𝟙 e (.arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀) φ₁ →
      typing Ω Γ 𝟙 (.lift e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤
    | app₁ : ∀ Ω Γ 𝕊 f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂,
      typing Ω Γ 𝕊 f (.arrow τ𝕒 τ𝕓 φ₀) φ₁ →
      typing Ω Γ 𝕊 arg τ𝕒 φ₂ →
      typing Ω Γ 𝕊 (.app₁ f arg) τ𝕓 (φ₀ ∪ φ₁ ∪ φ₂)
    | app₂ : ∀ Ω Γ f arg τ𝕒 τ𝕓 φ₀ φ₁,
      typing Ω Γ 𝟙 f (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) φ₀ →
      typing Ω Γ 𝟙 arg (.fragment τ𝕒) φ₁ →
      typing Ω Γ 𝟙 (.app₂ f arg) (.fragment τ𝕓) ⊤
    | lit : ∀ Ω Γ 𝕊 n,
      typing Ω Γ 𝕊 (.lit n) .nat ⊥
    | lift_lit : ∀ Ω Γ n φ,
      typing Ω Γ 𝟙 n .nat φ →
      typing Ω Γ 𝟙 (.lift n) (.fragment .nat) ⊤
    | code_fragment : ∀ Ω Γ x τ,
      binds x (τ, 𝟚) Γ →
      wbt 𝟚 τ →
      typing Ω Γ 𝟙 (.code (.fvar x)) (.fragment τ) ⊥
    | code_rep : ∀ Ω Γ e τ,
      typing Ω Γ 𝟚 e τ ⊥ →
      typing Ω Γ 𝟙 (.code e) (.rep τ) ⊥
    | reflect : ∀ Ω Γ e τ,
      typing Ω Γ 𝟚 e τ ⊥ →
      typing Ω Γ 𝟙 (.reflect e) (.fragment τ) ⊤
    | lam𝕔 : ∀ Ω Γ e τ𝕒 τ𝕓 φ,
      typing_reification Ω ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing Ω Γ 𝟙 (.lam𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤
    | lets : ∀ Ω Γ 𝕊 b e τ𝕒 τ𝕓 φ₀ φ₁,
      typing Ω Γ 𝕊 b τ𝕒 φ₀ →
      typing Ω ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ₁ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Ω Γ 𝕊 (.lets b e) τ𝕓 (φ₀ ∪ φ₁)
    | lets𝕔 : ∀ Ω Γ b e τ𝕒 τ𝕓 φ,
      typing Ω Γ 𝟚 b τ𝕒 ⊥ →
      typing_reification Ω ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing Ω Γ 𝟙 (.lets𝕔 b e) (.rep τ𝕓) ⊥
    | run : ∀ Ω Γ e τ φ,
      typing_reification Ω Γ e (.rep τ) φ →
      closed e →
      typing Ω Γ 𝟙 (.run e) τ ⊥
    | unit : ∀ Ω Γ 𝕊,
      typing Ω Γ 𝕊 .unit .unit ⊥
    | loc : ∀ Ω Γ l,
      binds l .nat Ω →
      typing Ω Γ 𝟙 (.loc l) (.ref .nat) ⊥
    | load₁ : ∀ Ω Γ 𝕊 e φ,
      typing Ω Γ 𝕊 e (.ref .nat) φ →
      typing Ω Γ 𝕊 (.load₁ e) .nat φ
    | load₂ : ∀ Ω Γ e φ,
      typing Ω Γ 𝟙 e (.fragment (.ref .nat)) φ →
      typing Ω Γ 𝟙 (.load₂ e) (.fragment .nat) ⊤
    | alloc₁ : ∀ Ω Γ 𝕊 e φ,
      typing Ω Γ 𝕊 e .nat φ →
      typing Ω Γ 𝕊 (.alloc₁ e) (.ref .nat) φ
    | alloc₂ : ∀ Ω Γ e φ,
      typing Ω Γ 𝟙 e (.fragment .nat) φ →
      typing Ω Γ 𝟙 (.alloc₂ e) (.fragment (.ref .nat)) ⊤
    | store₁ : ∀ Ω Γ 𝕊 l r φ₀ φ₁,
      typing Ω Γ 𝕊 l (.ref .nat) φ₀ →
      typing Ω Γ 𝕊 r .nat φ₁ →
      typing Ω Γ 𝕊 (.store₁ l r) .unit (φ₀ ∪ φ₁)
    | store₂ : ∀ Ω Γ l r φ₀ φ₁,
      typing Ω Γ 𝟙 l (.fragment (.ref .nat)) φ₀ →
      typing Ω Γ 𝟙 r (.fragment .nat) φ₁ →
      typing Ω Γ 𝟙 (.store₂ l r) (.fragment .unit) ⊤

  inductive typing_reification : HEnv → TEnv → Expr → Ty → Effect → Prop
    | pure : ∀ Ω Γ e τ, typing Ω Γ 𝟙 e τ ⊥ → typing_reification Ω Γ e τ ⊥
    | reify : ∀ Ω Γ e τ φ, typing Ω Γ 𝟙 e (.fragment τ) φ → typing_reification Ω Γ e (.rep τ) φ
end
