import CollapsingTowers.TwoLevelMut.SyntacticSoundness.Defs
import CollapsingTowers.TwoLevelMut.LogicalEquiv.World

-- (σ₀, σ₁) : 𝓦 ≜ ∀ 𝓦(l₀, l₁). σ₀(l₁) = σ₀(l₁)
@[simp]
def log_equiv_store (𝓦 : World) (σ₀ σ₁ : Store) : Prop :=
  ∀ l₀ l₁, 𝓦 l₀ l₁ →
  ∃ n, binds l₀ (.lit n) σ₀ ∧ binds l₁ (.lit n) σ₁

mutual
@[simp]
def log_equiv_value : World → Expr → Expr → Ty → Prop
  --
  --
  -- 𝓥⟦ℕ⟧ ≜ {(𝓦, n, n) | n ∈ ℕ}
  | _, .lit n₀, .lit n₁, .nat => n₀ = n₁
  --
  --
  -- 𝓥⟦τ𝕒 → τ𝕓⟧ ≜ {
  --   (𝓦₀, λx.e₀, λx.e₁) |
  --   ∀ (𝓦₁ ⊒ 𝓦₀), (𝓦₁, v₀, v₁) ∈ 𝓥⟦τ𝕒⟧. (𝓦₁, λx.e₀ @ v₀, λx.e₁ @ v₁) ∈ 𝓔⟦τ𝕓⟧
  -- }
  | 𝓦₀, .lam e₀, .lam e₁, (.arrow τ𝕒 τ𝕓 ⊥) =>
    wf (.lam e₀) ∧
    wf (.lam e₁) ∧
    ∀ 𝓦₁ v₀ v₁,
      (𝓦₁ ⊒ 𝓦₀) →
      log_equiv_value 𝓦₁ v₀ v₁ τ𝕒 →
      log_equiv_expr 𝓦₁ (.app₁ (.lam e₀) v₀) (.app₁ (.lam e₁) v₁) τ𝕓
  --
  --
  -- 𝓥⟦unit⟧ ≜ {(𝓦, (), ())}
  | _, .unit, .unit, .unit => true
  --
  --
  -- 𝓥⟦ref ℕ⟧ ≜ {(𝓦, l₀, l₁) | 𝓦(l₀, l₁)}
  | 𝓦, .loc l₀, .loc l₁, .ref .nat => 𝓦 l₀ l₁
  | _, _, _, _ => false

-- 𝓔⟦τ⟧ ≜ {
--   (𝓦₀, e₀, e₁) |
--   ∀ (σ₀, σ₁) : 𝓦₀.
--   ∃ ω₀, ω₁, v₀, v₁, (𝓦₁ ⊒ 𝓦₀).
--   ⟨σ₀, e₀⟩ ⇝* ⟨ω₀, v₀⟩ ∧
--   ⟨σ₁, e₁⟩ ⇝* ⟨ω₁, v₁⟩ ∧
--   (ω₀, ω₁) : 𝓦₁ ∧
--   (𝓦₁, v₀, v₁) ∈ 𝓥⟦τ⟧
-- }
@[simp]
def log_equiv_expr (𝓦₀ : World) (e₀ e₁ : Expr) (τ : Ty) : Prop :=
  ∀ σ₀ σ₁,
    log_equiv_store 𝓦₀ σ₀ σ₁ →
    ∃ 𝓦₁ ω₀ ω₁ v₀ v₁,
      (𝓦₁ ⊒ 𝓦₀) ∧
      (⟨σ₀, e₀⟩ ⇝* ⟨ω₀, v₀⟩) ∧
      (⟨σ₁, e₁⟩ ⇝* ⟨ω₁, v₁⟩) ∧
      log_equiv_store 𝓦₁ ω₀ ω₁ ∧
      log_equiv_value 𝓦₁ v₀ v₁ τ
end

inductive log_equiv_env : World → Subst → Subst → TEnv → Prop where
  | nil : ∀ 𝓦, log_equiv_env 𝓦 [] [] ⦰
  | cons : ∀ 𝓦 v₀ γ₀ v₁ γ₁ τ Γ,
    log_equiv_value 𝓦 v₀ v₁ τ →
    log_equiv_env 𝓦 γ₀ γ₁ Γ →
    log_equiv_env 𝓦 (v₀ :: γ₀) (v₁ :: γ₁) ((τ, 𝟚) :: Γ)

-- Γ ⊧ e₀ ≈𝑙𝑜𝑔 e₁ : τ ≜
--   Γ ⊢ e₀ : τ ∧
--   Γ ⊢ e₁ : τ ∧
--   ∀ 𝓦, (𝓦, γ₀, γ₁) ∈ 𝓖⟦Γ⟧. (𝓦, γ₀(e₀), γ₁(e₁)) ∈ 𝓔⟦τ⟧
@[simp]
def log_equiv (Γ : TEnv) (e₀ e₁ : Expr) (τ : Ty) : Prop :=
  typing ϵ Γ 𝟚 e₀ τ ⊥ ∧
  typing ϵ Γ 𝟚 e₁ τ ⊥ ∧
  ∀ 𝓦 γ₀ γ₁,
    log_equiv_env 𝓦 γ₀ γ₁ Γ →
    log_equiv_expr 𝓦 (msubst γ₀ e₀) (msubst γ₁ e₁) τ

lemma log_equiv_env.length :
  ∀ 𝓦 γ₀ γ₁ Γ,
    log_equiv_env 𝓦 γ₀ γ₁ Γ →
    γ₀.length = Γ.length ∧
    γ₁.length = Γ.length :=
  by
  intros 𝓦 γ₀ γ₁ Γ H
  induction H
  case nil => simp
  case cons IH =>
    constructor
    . simp; apply IH.left
    . simp; apply IH.right

lemma log_equiv_env.binds_log_equiv_value :
  ∀ 𝓦 γ₀ γ₁ Γ x τ,
    log_equiv_env 𝓦 γ₀ γ₁ Γ →
    binds x (τ, 𝟚) Γ →
    log_equiv_value 𝓦 (msubst γ₀ (.fvar x)) (msubst γ₁ (.fvar x)) τ :=
  by
  intros 𝓦 γ₀ γ₁ Γ x τ HsemΓ Hbinds
  induction HsemΓ
  case nil => nomatch Hbinds
  case cons v₀ γ₀ v₁ γ₁ τ Γ Hsem_value HsemΓ IH =>
    have ⟨HEq₀, HEq₁⟩ := log_equiv_env.length _ _ _ _ HsemΓ
    simp [HEq₀, HEq₁]
    by_cases HEqx : Γ.length = x
    . simp [if_pos HEqx]
      simp [if_pos HEqx] at Hbinds
      rw [← Hbinds, identity.msubst, identity.msubst]
      apply Hsem_value
      admit
      admit
    . simp [if_neg HEqx]
      simp [if_neg HEqx] at Hbinds
      apply IH; apply Hbinds
