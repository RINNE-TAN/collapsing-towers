import CollapsingTowers.TwoLevelBasic.SyntacticSoundness.Defs

mutual
@[simp]
def log_equiv_value : Expr → Expr → Ty → Prop
  --
  --
  -- 𝓥⟦ℕ⟧ ≜ {(n, n) | n ∈ ℕ}
  | .lit n₀, .lit n₁, .nat => n₀ = n₁
  --
  --
  -- 𝓥⟦τ𝕒 → τ𝕓⟧ ≜ {
  --   (λx.e₀, λx.e₁) |
  --   ⦰ ⊢ λx.e₀ : τ𝕒 → τ𝕓 ∧
  --   ⦰ ⊢ λx.e₁ : τ𝕒 → τ𝕓 ∧
  --   ∀ (v₀, v₁) ∈ 𝓥⟦τ𝕒⟧. (λx.e₀ @ v₀, λx.e₁ @ v₁) ∈ 𝓔⟦τ𝕓⟧
  -- }
  | .lam e₀, .lam e₁, (.arrow τ𝕒 τ𝕓 ⊥) =>
    typing ⦰ 𝟚 (.lam e₀) (.arrow τ𝕒 τ𝕓 ⊥) ⊥ ∧
    typing ⦰ 𝟚 (.lam e₁) (.arrow τ𝕒 τ𝕓 ⊥) ⊥ ∧
    ∀ v₀ v₁,
      log_equiv_value v₀ v₁ τ𝕒 →
      log_equiv_expr (.app₁ (.lam e₀) v₀) (.app₁ (.lam e₁) v₁) τ𝕓
  | _, _, _ => false

-- 𝓔⟦τ⟧ₖ ≜ {(e₀, e₁) | ∃ v₀ v₁. e₀ ⇾* v₀ ∧ e₁ ⇾* v₁ ∧ (v₀, v₁) ∈ 𝓥⟦τ⟧}
@[simp]
def log_equiv_expr (e₀ e₁ : Expr) (τ : Ty) : Prop :=
  ∃ v₀ v₁,
    (e₀ ⇝* v₀) ∧ (e₁ ⇝* v₁) ∧ log_equiv_value v₀ v₁ τ
end

inductive typing.subst : Subst → TEnv → Prop where
  | nil : typing.subst [] ⦰
  | cons : ∀ v γ τ Γ,
    value v →
    typing ⦰ 𝟚 v τ ⊥ →
    typing.subst γ Γ →
    typing.subst (v :: γ) ((τ, 𝟚) :: Γ)

inductive log_equiv_env : Subst → Subst → TEnv → Prop where
  | nil : log_equiv_env [] [] ⦰
  | cons : ∀ v₀ γ₀ v₁ γ₁ τ Γ,
    log_equiv_value v₀ v₁ τ →
    log_equiv_env γ₀ γ₁ Γ →
    log_equiv_env (v₀ :: γ₀) (v₁ :: γ₁) ((τ, 𝟚) :: Γ)

-- Γ ⊧ e₀ ≈𝑙𝑜𝑔 e₁ : τ ≜
--   Γ ⊢ e₀ : τ ∧
--   Γ ⊢ e₁ : τ ∧
--   ∀ (γ₀, γ₁) ∈ 𝓖⟦Γ⟧. (γ₀(e₀), γ₁(e₁)) ∈ 𝓔⟦τ⟧
@[simp]
def log_equiv (Γ : TEnv) (e₀ e₁ : Expr) (τ : Ty) : Prop :=
  typing Γ 𝟚 e₀ τ ⊥ ∧
  typing Γ 𝟚 e₁ τ ⊥ ∧
  ∀ γ₀ γ₁,
    log_equiv_env γ₀ γ₁ Γ →
    log_equiv_expr (msubst γ₀ e₀) (msubst γ₁ e₁) τ

lemma log_equiv_value.syntactic.value :
  ∀ v₀ v₁ τ,
    log_equiv_value v₀ v₁ τ →
    value v₀ ∧ value v₁ :=
  by
  intros v₀ v₁ τ Hsem_value
  cases τ
  case nat =>
    cases v₀ <;> cases v₁ <;> simp at Hsem_value
    constructor
    apply value.lit
    apply value.lit
  case arrow φ =>
    cases v₀ <;> cases v₁ <;> cases φ <;> simp at Hsem_value
    have ⟨Hτ₀, Hτ₁, _⟩ := Hsem_value
    constructor
    apply value.lam; apply typing.regular _ _ _ _ _ Hτ₀
    apply value.lam; apply typing.regular _ _ _ _ _ Hτ₁
  all_goals simp at Hsem_value

lemma log_equiv_value.syntactic.typing :
  ∀ v₀ v₁ τ,
    log_equiv_value v₀ v₁ τ →
    typing ⦰ 𝟚 v₀ τ ⊥ ∧ typing ⦰ 𝟚 v₁ τ ⊥ :=
  by
  intros v₀ v₁ τ Hsem_value
  cases τ
  case nat =>
    cases v₀ <;> cases v₁ <;> simp at Hsem_value
    constructor; apply typing.lit; apply typing.lit
  case arrow φ =>
    cases v₀ <;> cases v₁ <;> cases φ <;> simp at Hsem_value
    have ⟨Hτ₀, Hτ₁, _⟩ := Hsem_value
    constructor; apply Hτ₀; apply Hτ₁
  all_goals simp at Hsem_value

lemma log_equiv_value.apply :
  ∀ f₀ arg₀ f₁ arg₁ τ𝕒 τ𝕓,
    log_equiv_value f₀ f₁ (.arrow τ𝕒 τ𝕓 ⊥) →
    log_equiv_value arg₀ arg₁ τ𝕒 →
    log_equiv_expr (.app₁ f₀ arg₀) (.app₁ f₁ arg₁) τ𝕓 :=
  by
  intros f₀ arg₀ f₁ arg₁ τ𝕒 τ𝕓 Hsem_value_fun Hsem_value_arg
  cases f₀ <;> cases f₁ <;> simp only [log_equiv_value] at Hsem_value_fun <;> try contradiction
  have ⟨_, _, Hsem_value_fun⟩ := Hsem_value_fun
  apply Hsem_value_fun; apply Hsem_value_arg

lemma log_equiv_env.length :
  ∀ γ₀ γ₁ Γ,
    log_equiv_env γ₀ γ₁ Γ →
    γ₀.length = Γ.length ∧
    γ₁.length = Γ.length :=
  by
  intros γ₀ γ₁ Γ H
  induction H
  case nil => simp
  case cons IH =>
    constructor
    . simp; apply IH.left
    . simp; apply IH.right

lemma log_equiv_env.binds_log_equiv_value :
  ∀ γ₀ γ₁ Γ x τ,
    log_equiv_env γ₀ γ₁ Γ →
    binds x (τ, 𝟚) Γ →
    log_equiv_value (msubst γ₀ (.fvar x)) (msubst γ₁ (.fvar x)) τ :=
  by
  intros γ₀ γ₁ Γ x τ HsemΓ Hbinds
  induction HsemΓ
  case nil => nomatch Hbinds
  case cons v₀ γ₀ v₁ γ₁ τ Γ Hsem_value HsemΓ IH =>
    have ⟨Hτ₀, Hτ₁⟩ := log_equiv_value.syntactic.typing _ _ _ Hsem_value
    have ⟨HEq₀, HEq₁⟩ := log_equiv_env.length _ _ _ HsemΓ
    simp [HEq₀, HEq₁]
    by_cases HEqx : Γ.length = x
    . simp [if_pos HEqx]
      simp [if_pos HEqx] at Hbinds
      rw [← Hbinds, identity.msubst, identity.msubst]
      apply Hsem_value
      apply typing.closed_at_env _ _ _ _ _ Hτ₁
      apply typing.closed_at_env _ _ _ _ _ Hτ₀
    . simp [if_neg HEqx]
      simp [if_neg HEqx] at Hbinds
      apply IH; apply Hbinds

lemma log_equiv_env.mwf :
  ∀ γ₀ γ₁ Γ,
    log_equiv_env γ₀ γ₁ Γ →
    mwf γ₀ ∧ mwf γ₁ :=
  by
  intros γ₀ γ₁ Γ HsemΓ
  induction HsemΓ
  case nil => repeat constructor
  case cons Hsem_value _ IH =>
    have ⟨Hτ₀, Hτ₁⟩ := log_equiv_value.syntactic.typing _ _ _ Hsem_value
    constructor
    . constructor
      apply typing.wf _ _ _ _ _ Hτ₀
      apply IH.left
    . constructor
      apply typing.wf _ _ _ _ _ Hτ₁
      apply IH.right

lemma log_equiv_env.msubst.typing :
  ∀ γ₀ γ₁ e₀ e₁ Γ τ,
    typing Γ 𝟚 e₀ τ ⊥ →
    typing Γ 𝟚 e₁ τ ⊥ →
    log_equiv_env γ₀ γ₁ Γ →
    typing ⦰ 𝟚 (msubst γ₀ e₀) τ ⊥ ∧
    typing ⦰ 𝟚 (msubst γ₁ e₁) τ ⊥ :=
  by
  intros γ₀ γ₁ e₀ e₁ Γ τ Hτ₀ Hτ₁ HsemΓ
  induction HsemΓ generalizing e₀ e₁
  case nil => constructor; apply Hτ₀; apply Hτ₁
  case cons Γ Hsem_value HsemΓ IH =>
    have ⟨HEq₀, HEq₁⟩ := log_equiv_env.length _ _ _ HsemΓ
    have ⟨Hτv₀, Hτv₁⟩ := log_equiv_value.syntactic.typing _ _ _ Hsem_value
    apply IH
    . rw [HEq₀]; apply preservation.dynamic_subst; rw [← List.append_nil Γ]
      apply typing.weakening; apply Hτv₀; apply Hτ₀
    . rw [HEq₁]; apply preservation.dynamic_subst; rw [← List.append_nil Γ]
      apply typing.weakening; apply Hτv₁; apply Hτ₁

lemma log_equiv_env.syntactic.typing :
  ∀ γ₀ γ₁ Γ,
    log_equiv_env γ₀ γ₁ Γ →
    typing.subst γ₀ Γ ∧
    typing.subst γ₁ Γ :=
  by
  intros γ₀ γ₁ Γ HsemΓ
  induction HsemΓ
  case nil =>
    constructor
    . apply typing.subst.nil
    . apply typing.subst.nil
  case cons Hsem_value _ IH =>
    have ⟨IH₀, IH₁⟩ := IH
    have ⟨Hτv₀, Hτv₁⟩ := log_equiv_value.syntactic.typing _ _ _ Hsem_value
    have ⟨Hvalue₀, Hvalue₁⟩ := log_equiv_value.syntactic.value _ _ _ Hsem_value
    constructor
    . apply typing.subst.cons
      apply Hvalue₀; apply Hτv₀
      apply IH₀
    . apply typing.subst.cons
      apply Hvalue₁; apply Hτv₁
      apply IH₁

lemma typing.subst.length :
  ∀ γ Γ,
    typing.subst γ Γ →
    γ.length = Γ.length :=
  by
  intros γ Γ Hτγ
  induction Hτγ
  case nil => simp
  case cons IH => simp [IH]
