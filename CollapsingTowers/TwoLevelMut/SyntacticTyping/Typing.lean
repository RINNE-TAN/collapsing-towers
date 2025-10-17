import CollapsingTowers.TwoLevelMut.Syntax.Defs
import CollapsingTowers.TwoLevelMut.SyntacticTyping.Env
import CollapsingTowers.TwoLevelMut.OperationalSemantics.Defs
mutual
  inductive typing : Store → TEnv → Stage → Expr → Ty → REffects → MEffects → Prop where
    | fvar : ∀ σ Γ 𝕊 x τ,
      binds x (τ, 𝕊) Γ →
      wbt 𝕊 τ →
      typing σ Γ 𝕊 (.fvar x) τ ⊥ ∅
    | lam : ∀ σ Γ 𝕊 e τ𝕒 τ𝕓 φ ω,
      typing σ ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ ω →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing σ Γ 𝕊 (.lam e) (.arrow τ𝕒 τ𝕓 φ ω) ⊥ ∅
    | lift_lam : ∀ σ Γ e τ𝕒 τ𝕓 φ₀ φ₁ ω₀ ω₁,
      typing σ Γ 𝟙 e (.arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀ ω₀) φ₁ ω₁ →
      wbt_meffects 𝟚 ω₀ →
      typing σ Γ 𝟙 (.lift e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥ ω₀)) ⊤ ω₁
    | app₁ : ∀ σ Γ 𝕊 f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂ ω₀ ω₁ ω₂,
      typing σ Γ 𝕊 f (.arrow τ𝕒 τ𝕓 φ₀ ω₀) φ₁ ω₁ →
      typing σ Γ 𝕊 arg τ𝕒 φ₂ ω₂ →
      typing σ Γ 𝕊 (.app₁ f arg) τ𝕓 (φ₀ ∪ φ₁ ∪ φ₂) (ω₀ ∪ ω₁ ∪ ω₂)
    | app₂ : ∀ σ Γ f arg τ𝕒 τ𝕓 φ₁ φ₂ ω₀ ω₁ ω₂,
      typing σ Γ 𝟙 f (.fragment (.arrow τ𝕒 τ𝕓 ⊥ ω₀)) φ₁ ω₁ →
      typing σ Γ 𝟙 arg (.fragment τ𝕒) φ₂ ω₂ →
      typing σ Γ 𝟙 (.app₂ f arg) (.fragment τ𝕓) ⊤ (ω₀ ∪ ω₁ ∪ ω₂)
    | lit : ∀ σ Γ 𝕊 n,
      typing σ Γ 𝕊 (.lit n) .nat ⊥ ∅
    | lift_lit : ∀ σ Γ n φ ω,
      typing σ Γ 𝟙 n .nat φ ω →
      typing σ Γ 𝟙 (.lift n) (.fragment .nat) ⊤ ω
    | code_fragment : ∀ σ Γ x τ,
      binds x (τ, 𝟚) Γ →
      wbt 𝟚 τ →
      typing σ Γ 𝟙 (.code (.fvar x)) (.fragment τ) ⊥ ∅
    | code_rep : ∀ σ Γ e τ ω,
      typing σ Γ 𝟚 e τ ⊥ ω →
      typing σ Γ 𝟙 (.code e) (.rep τ) ⊥ (escape_meffects ω)
    | reflect : ∀ σ Γ e τ ω,
      typing σ Γ 𝟚 e τ ⊥ ω →
      typing σ Γ 𝟙 (.reflect e) (.fragment τ) ⊤ ω
    | lam𝕔 : ∀ σ Γ e τ𝕒 τ𝕓 φ ω,
      typing_reification σ ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ ω →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing σ Γ 𝟙 (.lam𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥ ω)) ⊤ ∅
    | lets : ∀ σ Γ 𝕊 b e τ𝕒 τ𝕓 φ₀ φ₁ ω₀ ω₁,
      typing σ Γ 𝕊 b τ𝕒 φ₀ ω₀ →
      typing σ ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ₁ ω₁ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing σ Γ 𝕊 (.lets b e) τ𝕓 (φ₀ ∪ φ₁) (ω₀ ∪ ω₁)
    | lets𝕔 : ∀ σ Γ b e τ𝕒 τ𝕓 φ₁ ω₀ ω₁,
      typing σ Γ 𝟚 b τ𝕒 ⊥ ω₀ →
      typing_reification σ ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ₁ ω₁ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing σ Γ 𝟙 (.lets𝕔 b e) (.rep τ𝕓) ⊥ (ω₀ ∪ ω₁)
    | run : ∀ σ Γ e τ φ ω,
      typing_reification σ Γ e (.rep τ) φ ω →
      closed e →
      typing σ Γ 𝟙 (.run e) τ ⊥ (erase_meffects ω)
    | unit : ∀ σ Γ 𝕊,
      typing σ Γ 𝕊 .unit .unit ⊥ ∅
    | lift_unit : ∀ σ Γ e φ ω,
      typing σ Γ 𝟙 e .unit φ ω →
      typing σ Γ 𝟙 (.lift e) (.fragment .unit) ⊤ ω
    | loc : ∀ σ Γ l,
      l < σ.length →
      typing σ Γ 𝟙 (.loc l) (.ref .nat) ⊥ ∅
    | alloc₁ : ∀ σ Γ 𝕊 e φ ω,
      typing σ Γ 𝕊 e .nat φ ω →
      typing σ Γ 𝕊 (.alloc₁ e) (.ref .nat) φ (ω ∪ { .init 𝕊 })
    | alloc₂ : ∀ σ Γ e φ ω,
      typing σ Γ 𝟙 e (.fragment .nat) φ ω →
      typing σ Γ 𝟙 (.alloc₂ e) (.fragment (.ref .nat)) ⊤ (ω ∪ { .init 𝟚 })
    | load₁ : ∀ σ Γ 𝕊 e φ ω,
      typing σ Γ 𝕊 e (.ref .nat) φ ω →
      typing σ Γ 𝕊 (.load₁ e) .nat φ (ω ∪ { .read 𝕊 })
    | load₂ : ∀ σ Γ e φ ω,
      typing σ Γ 𝟙 e (.fragment .nat) φ ω →
      typing σ Γ 𝟙 (.load₂ e) (.fragment (.ref .nat)) ⊤ (ω ∪ { .read 𝟚 })
    | store₁ : ∀ σ Γ 𝕊 l r φ₀ φ₁ ω₀ ω₁,
      typing σ Γ 𝕊 l (.ref .nat) φ₀ ω₀ →
      typing σ Γ 𝕊 r .nat φ₁ ω₁ →
      typing σ Γ 𝕊 (.store₁ l r) .unit (φ₀ ∪ φ₁) (ω₀ ∪ ω₁ ∪ { .write 𝕊 })
    | store₂ : ∀ σ Γ l r φ₀ φ₁ ω₀ ω₁,
      typing σ Γ 𝟙 l (.fragment (.ref .nat)) φ₀ ω₀ →
      typing σ Γ 𝟙 r (.fragment .nat) φ₁ ω₁ →
      typing σ Γ 𝟙 (.store₂ l r) (.fragment .unit) ⊤ (ω₀ ∪ ω₁ ∪ { .write 𝟚 })

  inductive typing_reification : Store → TEnv → Expr → Ty → REffects → MEffects → Prop
    | pure : ∀ σ Γ e τ ω, typing σ Γ 𝟙 e τ ⊥ ω → typing_reification σ Γ e τ ⊥ ω
    | reify : ∀ σ Γ e τ φ ω, typing σ Γ 𝟙 e (.fragment τ) φ ω → typing_reification σ Γ e (.rep τ) φ ω
end
