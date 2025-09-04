import CollapsingTowers.TwoLevelMut.SyntacticSoundness.Defs
import CollapsingTowers.TwoLevelMut.LogicalEquiv.World

-- (σ₀, σ₁) : 𝓦 ≜ ∀ 𝓦(l₀, l₁). σ₀(l₁) = σ₀(l₁)
@[simp]
def log_equiv_store (𝓦 : World) (σ₀ σ₁ : Store) : Prop :=
  bijection 𝓦 ∧ (
  ∀ l₀ l₁,
    𝓦 l₀ l₁ →
    ∃ n,
      binds l₀ (.lit n) σ₀ ∧
      binds l₁ (.lit n) σ₁
  )

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
    wf (.lam e₀) ∧ grounded (.lam e₀) ∧
    wf (.lam e₁) ∧ grounded (.lam e₁) ∧
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
--   ∃ σ₂, σ₃, v₀, v₁, (𝓦₁ ⊒ 𝓦₀).
--     ⟨σ₀, e₀⟩ ⇝* ⟨σ₂, v₀⟩ ∧
--     ⟨σ₁, e₁⟩ ⇝* ⟨σ₃, v₁⟩ ∧
--     (σ₂, σ₃) : 𝓦₁ ∧
--     (𝓦₁, v₀, v₁) ∈ 𝓥⟦τ⟧
-- }
@[simp]
def log_equiv_expr (𝓦₀ : World) (e₀ e₁ : Expr) (τ : Ty) : Prop :=
  ∀ σ₀ σ₁,
    log_equiv_store 𝓦₀ σ₀ σ₁ →
    ∃ 𝓦₁ σ₂ σ₃ v₀ v₁,
      (𝓦₁ ⊒ 𝓦₀) ∧
      (⟨σ₀, e₀⟩ ⇝* ⟨σ₂, v₀⟩) ∧
      (⟨σ₁, e₁⟩ ⇝* ⟨σ₃, v₁⟩) ∧
      log_equiv_store 𝓦₁ σ₂ σ₃ ∧
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

lemma log_equiv_value.antimono :
  ∀ 𝓦₀ 𝓦₁ v₀ v₁ τ,
    log_equiv_value 𝓦₀ v₀ v₁ τ →
    (𝓦₁ ⊒ 𝓦₀) →
    log_equiv_value 𝓦₁ v₀ v₁ τ :=
  by
  intros 𝓦₀ 𝓦₁ v₀ v₁ τ Hsem_value Hfuture₀
  cases τ
  case nat =>
    cases v₀ <;> try simp at Hsem_value
    case lit n₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lit n₁ =>
    simp; apply Hsem_value
  case arrow τ𝕒 τ𝕓 φ =>
    cases v₀ <;> try simp at Hsem_value
    case lam e₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lam e₁ =>
    cases φ <;> simp only [log_equiv_value] at Hsem_value <;> try contradiction
    have ⟨Hwf₀, HG₀, Hwf₁, HG₁, Hsem_value⟩ := Hsem_value
    simp only [log_equiv_value]
    constructor; apply Hwf₀
    constructor; apply HG₀
    constructor; apply Hwf₁
    constructor; apply HG₁
    intros 𝓦₂ v₀ v₁ Hfuture₁
    apply Hsem_value
    apply World.future.trans _ _ _ Hfuture₁ Hfuture₀
  case unit =>
    cases v₀ <;> try simp at Hsem_value
    case unit =>
    cases v₁ <;> try simp at Hsem_value
    case unit =>
    simp
  case ref τ =>
    cases v₀ <;> try simp at Hsem_value
    case loc l₀ =>
    cases v₁ <;> try simp at Hsem_value
    case loc l₁ =>
    cases τ <;> simp only [log_equiv_value] at Hsem_value <;> try contradiction
    simp only [log_equiv_value]
    apply Hfuture₀; apply Hsem_value
  case fragment => simp at Hsem_value
  case rep => simp at Hsem_value

lemma log_equiv_env.antimono :
  ∀ 𝓦₀ 𝓦₁ γ₀ γ₁ Γ,
    log_equiv_env 𝓦₀ γ₀ γ₁ Γ →
    (𝓦₁ ⊒ 𝓦₀) →
    log_equiv_env 𝓦₁ γ₀ γ₁ Γ :=
  by
  intros 𝓦₀ 𝓦₁ γ₀ γ₁ Γ HsemΓ Hfuture₀
  induction HsemΓ
  case nil => apply log_equiv_env.nil
  case cons Hsem_value _ IH =>
    apply log_equiv_env.cons
    apply log_equiv_value.antimono; apply Hsem_value; apply Hfuture₀
    apply IH

lemma log_equiv_value.syntactic.value :
  ∀ 𝓦 v₀ v₁ τ,
    log_equiv_value 𝓦 v₀ v₁ τ →
    value v₀ ∧ value v₁ :=
  by
  intros 𝓦 v₀ v₁ τ Hsem_value
  cases τ
  case nat =>
    cases v₀ <;> try simp at Hsem_value
    case lit n₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lit n₁ =>
    constructor
    apply value.lit
    apply value.lit
  case arrow τ𝕒 τ𝕓 φ =>
    cases v₀ <;> try simp at Hsem_value
    case lam e₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lam e₁ =>
    cases φ <;> simp only [log_equiv_value] at Hsem_value <;> try contradiction
    have ⟨Hwf₀, HG₀, Hwf₁, HG₁, Hsem_value⟩ := Hsem_value
    constructor
    apply value.lam; apply Hwf₀.left
    apply value.lam; apply Hwf₁.left
  case unit =>
    cases v₀ <;> try simp at Hsem_value
    case unit =>
    cases v₁ <;> try simp at Hsem_value
    case unit =>
    constructor
    apply value.unit
    apply value.unit
  case ref τ =>
    cases v₀ <;> try simp at Hsem_value
    case loc l₀ =>
    cases v₁ <;> try simp at Hsem_value
    case loc l₁ =>
    cases τ <;> simp only [log_equiv_value] at Hsem_value <;> try contradiction
    constructor
    apply value.loc
    apply value.loc
  case fragment => simp at Hsem_value
  case rep => simp at Hsem_value

lemma log_equiv_value.syntactic.wf :
  ∀ k v₀ v₁ τ,
    log_equiv_value k v₀ v₁ τ →
    wf v₀ ∧ wf v₁ :=
  by
  intros 𝓦 v₀ v₁ τ Hsem_value
  cases τ
  case nat =>
    cases v₀ <;> try simp at Hsem_value
    case lit n₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lit n₁ =>
    simp
  case arrow τ𝕒 τ𝕓 φ =>
    cases v₀ <;> try simp at Hsem_value
    case lam e₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lam e₁ =>
    cases φ <;> simp only [log_equiv_value] at Hsem_value <;> try contradiction
    have ⟨Hwf₀, HG₀, Hwf₁, HG₁, Hsem_value⟩ := Hsem_value
    constructor
    apply Hwf₀
    apply Hwf₁
  case unit =>
    cases v₀ <;> try simp at Hsem_value
    case unit =>
    cases v₁ <;> try simp at Hsem_value
    case unit =>
    simp
  case ref τ =>
    cases v₀ <;> try simp at Hsem_value
    case loc l₀ =>
    cases v₁ <;> try simp at Hsem_value
    case loc l₁ =>
    cases τ <;> simp only [log_equiv_value] at Hsem_value <;> try contradiction
    simp
  case fragment => simp at Hsem_value
  case rep => simp at Hsem_value

lemma log_equiv_value.syntactic.grounded :
  ∀ k v₀ v₁ τ,
    log_equiv_value k v₀ v₁ τ →
    grounded v₀ ∧ grounded v₁ :=
  by
  intros 𝓦 v₀ v₁ τ Hsem_value
  cases τ
  case nat =>
    cases v₀ <;> try simp at Hsem_value
    case lit n₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lit n₁ =>
    simp
  case arrow τ𝕒 τ𝕓 φ =>
    cases v₀ <;> try simp at Hsem_value
    case lam e₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lam e₁ =>
    cases φ <;> simp only [log_equiv_value] at Hsem_value <;> try contradiction
    have ⟨Hwf₀, HG₀, Hwf₁, HG₁, Hsem_value⟩ := Hsem_value
    constructor
    apply HG₀
    apply HG₁
  case unit =>
    cases v₀ <;> try simp at Hsem_value
    case unit =>
    cases v₁ <;> try simp at Hsem_value
    case unit =>
    simp
  case ref τ =>
    cases v₀ <;> try simp at Hsem_value
    case loc l₀ =>
    cases v₁ <;> try simp at Hsem_value
    case loc l₁ =>
    cases τ <;> simp only [log_equiv_value] at Hsem_value <;> try contradiction
    simp
  case fragment => simp at Hsem_value
  case rep => simp at Hsem_value

lemma log_equiv_value.apply :
  ∀ 𝓦 f₀ arg₀ f₁ arg₁ τ𝕒 τ𝕓,
    log_equiv_value 𝓦 f₀ f₁ (.arrow τ𝕒 τ𝕓 ⊥) →
    log_equiv_value 𝓦 arg₀ arg₁ τ𝕒 →
    log_equiv_expr 𝓦 (.app₁ f₀ arg₀) (.app₁ f₁ arg₁) τ𝕓 :=
  by
  intros 𝓦 f₀ arg₀ f₁ arg₁ τ𝕒 τ𝕓 Hsem_value_fun Hsem_value_arg
  cases f₀ <;> cases f₁ <;> simp only [log_equiv_value] at Hsem_value_fun <;> try contradiction
  have ⟨_, _, _, _, Hsem_value_fun⟩ := Hsem_value_fun
  apply Hsem_value_fun; apply World.future.refl; apply Hsem_value_arg

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
    have ⟨Hwf₀, Hwf₁⟩ := log_equiv_value.syntactic.wf _ _ _ _ Hsem_value
    have ⟨HEq₀, HEq₁⟩ := log_equiv_env.length _ _ _ _ HsemΓ
    simp [HEq₀, HEq₁]
    by_cases HEqx : Γ.length = x
    . simp [if_pos HEqx]
      simp [if_pos HEqx] at Hbinds
      rw [← Hbinds, identity.msubst, identity.msubst]
      apply Hsem_value
      apply Hwf₁.right
      apply Hwf₀.right
    . simp [if_neg HEqx]
      simp [if_neg HEqx] at Hbinds
      apply IH; apply Hbinds
