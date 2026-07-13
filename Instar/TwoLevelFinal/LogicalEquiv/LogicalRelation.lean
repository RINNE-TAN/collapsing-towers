import Instar.TwoLevelFinal.SyntacticSoundness.Defs
import Instar.TwoLevelFinal.LogicalEquiv.World

-- (σ₀, σ₁) : 𝓦 ≜ ∀ 𝓦(l₀, l₁). σ₀(l₁) = σ₀(l₁)
@[simp]
def log_well_store (𝓦 : World) (σ₀ σ₁ : Store) : Prop :=
  PartialBijection 𝓦 ∧ (
  ∀ l₀ l₁,
    𝓦 l₀ l₁ →
    ∃ n,
      binds l₀ (.lit n) σ₀ ∧
      binds l₁ (.lit n) σ₁
  )

abbrev KripkeWorld := Nat × World

@[simp]
def KripkeWorld.future : KripkeWorld → KripkeWorld → Prop
  | (k, 𝓦₀), (j, 𝓦₁) => j ≤ k ∧ 𝓦₁ ⊒ 𝓦₀

notation:max 𝓦₁ " ⊒ " 𝓦₀  => KripkeWorld.future 𝓦₀ 𝓦₁

mutual
@[simp]
def log_approx_value : KripkeWorld → Expr → Expr → Ty → Prop
  --
  --
  -- 𝓥⟦ℕ⟧ ≜ {(k, 𝓦, n, n) | n ∈ ℕ}
  | _, .lit n₀, .lit n₁, .nat => n₀ = n₁
  --
  --
  -- 𝓥⟦τ𝕒 → τ𝕓⟧ ≜ {
  --   (k, 𝓦₀, λx.e₀, λx.e₁) |
  --   ∀ (j, 𝓦₁) ⊒ (k, 𝓦₀), (j, 𝓦₁, v₀, v₁) ∈ 𝓥⟦τ𝕒⟧. (j, 𝓦₁, λx.e₀ @ v₀, λx.e₁ @ v₁) ∈ 𝓔⟦τ𝕓⟧
  -- }
  | (k, 𝓦₀), .lam e₀, .lam e₁, (.arrow τ𝕒 τ𝕓 ⊥) =>
    wf (.lam e₀) ∧ grounded (.lam e₀) ∧
    wf (.lam e₁) ∧ grounded (.lam e₁) ∧
    ∀ j 𝓦₁ v₀ v₁,
      ((j, 𝓦₁) ⊒ (k, 𝓦₀)) →
      log_approx_value (j, 𝓦₁) v₀ v₁ τ𝕒 →
      log_approx_expr (j, 𝓦₁) (.app₁ (.lam e₀) v₀) (.app₁ (.lam e₁) v₁) τ𝕓
  --
  --
  -- 𝓥⟦unit⟧ ≜ {(k, 𝓦, (), ())}
  | _, .unit, .unit, .unit => true
  --
  --
  -- 𝓥⟦ref ℕ⟧ ≜ {(k, 𝓦, l₀, l₁) | 𝓦(l₀, l₁)}
  | (_, 𝓦), .loc l₀, .loc l₁, .ref .nat => 𝓦 l₀ l₁
  | _, _, _, _ => false

-- 𝓔⟦τ⟧ ≜ {
--   (k, 𝓦₀, e₀, e₁) |
--   ∀ j ≤ k, (σ₀, σ₁) : 𝓦₀, σ₂, v₀.
--   ⟨σ₀, e₀⟩ ⭢ⱼ ⟨σ₂, v₀⟩ →
--   ∃ 𝓦₁, σ₃, v₁.
--     (k - j, 𝓦₁) ⊒ (k, 𝓦₀) ∧
--     ⟨σ₁, e₁⟩ ⭢* ⟨σ₃, v₁⟩ ∧
--     (σ₂, σ₃) : 𝓦₁ ∧
--     (k - j, 𝓦₁, v₀, v₁) ∈ 𝓥⟦τ⟧
-- }
@[simp]
def log_approx_expr : KripkeWorld → Expr → Expr → Ty → Prop
  | (k, 𝓦₀), e₀, e₁, τ =>
    ∀ j, j < k →
    ∀ σ₀ σ₁, log_well_store 𝓦₀ σ₀ σ₁ →
    ∀ σ₂ v₀, value v₀ → (⟨σ₀, e₀⟩ ⭢ ⟦j⟧ ⟨σ₂, v₀⟩) →
    ∃ 𝓦₁ σ₃ v₁,
      ((k - j, 𝓦₁) ⊒ (k, 𝓦₀)) ∧
      (⟨σ₁, e₁⟩ ⭢* ⟨σ₃, v₁⟩) ∧
      log_well_store 𝓦₁ σ₂ σ₃ ∧
      log_approx_value (k - j, 𝓦₁) v₀ v₁ τ
end

inductive log_approx_env : KripkeWorld → Subst → Subst → TEnv → Prop where
  | nil : ∀ k 𝓦, log_approx_env (k, 𝓦) [] [] ⦰
  | cons : ∀ k 𝓦 v₀ γ₀ v₁ γ₁ τ Γ,
    log_approx_value (k, 𝓦) v₀ v₁ τ →
    log_approx_env (k, 𝓦) γ₀ γ₁ Γ →
    log_approx_env (k, 𝓦) (v₀ :: γ₀) (v₁ :: γ₁) ((τ, 𝟚) :: Γ)

-- Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ ≜
--   Γ ⊢ e₀ : τ ∧
--   Γ ⊢ e₁ : τ ∧
--   ∀ k ≥ 0, 𝓦, (k, 𝓦, γ₀, γ₁) ∈ 𝓖⟦Γ⟧. (k, 𝓦, γ₀(e₀), γ₁(e₁)) ∈ 𝓔⟦τ⟧
@[simp]
def log_approx (Γ : TEnv) (e₀ e₁ : Expr) (τ : Ty) : Prop :=
  typing Γ 𝟚 e₀ τ ⊥ ∧
  typing Γ 𝟚 e₁ τ ⊥ ∧
  ∀ k 𝓦 γ₀ γ₁,
    log_approx_env (k, 𝓦) γ₀ γ₁ Γ →
    log_approx_expr (k, 𝓦) (msubst γ₀ e₀) (msubst γ₁ e₁) τ

-- Γ ⊧ e₀ ≈𝑙𝑜𝑔 e₁ : τ ≜ Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ ∧ Γ ⊧ e₁ ≤𝑙𝑜𝑔 e₀ : τ
@[simp]
def log_equiv (Γ : TEnv) (e₀ e₁ : Expr) (τ : Ty) : Prop :=
  log_approx Γ e₀ e₁ τ ∧ log_approx Γ e₁ e₀ τ

lemma log_well_store.alloc :
  ∀ 𝓦 σ₀ σ₁ n,
    log_well_store 𝓦 σ₀ σ₁ →
    log_well_store (World.ext 𝓦 σ₀.length σ₁.length) (.lit n :: σ₀) (.lit n :: σ₁) :=
  by
  intros 𝓦 σ₀ σ₁ n Hsem_store
  have ⟨Hpb, Hsem_store⟩ := Hsem_store
  constructor
  . apply PartialBijection.ext
    . apply Hpb
    . intros Hdom
      rcases Hdom with ⟨l₁, Hrel⟩
      have ⟨n, Hbinds₀, Hbinds₁⟩ := Hsem_store _ _ Hrel
      have _ := (getr_exists_iff_index_lt_length σ₀ σ₀.length).mpr (by exists .lit n)
      omega
    . intros Hrange
      rcases Hrange with ⟨l₀, Hrel⟩
      have ⟨n, Hbinds₀, Hbinds₁⟩ := Hsem_store _ _ Hrel
      have _ := (getr_exists_iff_index_lt_length σ₁ σ₁.length).mpr (by exists .lit n)
      omega
  . intros l₀ l₁ Hrel
    cases Hrel
    case inl HEq => simp [HEq]
    case inr Hrel =>
      have ⟨n, Hbinds₀, Hbinds₁⟩ := Hsem_store _ _ Hrel
      exists n; constructor
      . apply binds.extend _ [_] _ _ Hbinds₀
      . apply binds.extend _ [_] _ _ Hbinds₁

lemma log_well_store.store :
  ∀ 𝓦 l₀ l₁ σ₀ σ₁ σ₂ σ₃ n,
    log_well_store 𝓦 σ₀ σ₁ →
    𝓦 l₀ l₁ →
    patch l₀ (.lit n) σ₀ σ₂ →
    patch l₁ (.lit n) σ₁ σ₃ →
    log_well_store 𝓦 σ₂ σ₃ :=
  by
  intros 𝓦 l₀ l₁ σ₀ σ₁ σ₂ σ₃ n Hsem_store Hrel₀ Hpatch₀ Hpatch₁
  have ⟨Hpb, Hsem_store⟩ := Hsem_store
  constructor
  . apply Hpb
  . intros l₂ l₃ Hrel₁
    cases (PartialBijection.eq_or_disjoint _ _ _ _ _ Hpb Hrel₀ Hrel₁)
    case inl HEq =>
      simp [← HEq]
      exists n; constructor
      . apply patch.binds_eq _ _ _ _ Hpatch₀
      . apply patch.binds_eq _ _ _ _ Hpatch₁
    case inr HNe =>
      have ⟨n, Hbinds₀, Hbinds₁⟩ := Hsem_store _ _ Hrel₁
      exists n; constructor
      . apply patch.binds_disjoint _ _ _ _ _ _ Hpatch₀ HNe.left Hbinds₀
      . apply patch.binds_disjoint _ _ _ _ _ _ Hpatch₁ HNe.right Hbinds₁

lemma log_approx_value.antimono :
  ∀ k₀ k₁ 𝓦₀ 𝓦₁ v₀ v₁ τ,
    log_approx_value (k₀, 𝓦₀) v₀ v₁ τ →
    ((k₁, 𝓦₁) ⊒ (k₀, 𝓦₀)) →
    log_approx_value (k₁, 𝓦₁) v₀ v₁ τ :=
  by
  intros k₀ k₁ 𝓦₀ 𝓦₁ v₀ v₁ τ Hsem_value Hfuture₀
  cases τ
  case nat =>
    cases v₀ <;> try simp at Hsem_value
    case lit n₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lit n₁ =>
    simp; apply Hsem_value
  case arrow τ𝕒 τ𝕓 ε =>
    cases v₀ <;> try simp at Hsem_value
    case lam e₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lam e₁ =>
    cases ε <;> simp only [log_approx_value] at Hsem_value <;> try contradiction
    have ⟨Hwf₀, HG₀, Hwf₁, HG₁, Hsem_value⟩ := Hsem_value
    simp only [log_approx_value]
    constructor; apply Hwf₀
    constructor; apply HG₀
    constructor; apply Hwf₁
    constructor; apply HG₁
    intros k₂ 𝓦₂ v₀ v₁ Hfuture₁
    apply Hsem_value
    have ⟨Hindexk₀, Hfuture₀⟩ := Hfuture₀
    have ⟨Hindexk₁, Hfuture₁⟩ := Hfuture₁
    constructor
    . omega
    . apply World.future.trans _ _ _ Hfuture₁
      apply Hfuture₀
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
    cases τ <;> simp only [log_approx_value] at Hsem_value <;> try contradiction
    simp only [log_approx_value]
    apply Hfuture₀.right; apply Hsem_value
  case fragment => simp at Hsem_value
  case rep => simp at Hsem_value

lemma log_approx_env.antimono :
  ∀ k₀ k₁ 𝓦₀ 𝓦₁ γ₀ γ₁ Γ,
    log_approx_env (k₀, 𝓦₀) γ₀ γ₁ Γ →
    ((k₁, 𝓦₁) ⊒ (k₀, 𝓦₀)) →
    log_approx_env (k₁, 𝓦₁) γ₀ γ₁ Γ :=
  by
  intros k₀ k₁ 𝓦₀ 𝓦₁ γ₀ γ₁ Γ HsemΓ Hfuture
  generalize HEqi𝓦₀ : (k₀, 𝓦₀) = i𝓦₀
  rw [HEqi𝓦₀] at HsemΓ
  induction HsemΓ
  case nil => apply log_approx_env.nil
  case cons Hsem_value _ IH =>
    rw [← HEqi𝓦₀] at Hsem_value
    apply log_approx_env.cons
    apply log_approx_value.antimono; apply Hsem_value; apply Hfuture
    apply IH; apply HEqi𝓦₀

lemma log_approx_value.syntactic.value :
  ∀ k 𝓦 v₀ v₁ τ,
    log_approx_value (k, 𝓦) v₀ v₁ τ →
    value v₀ ∧ value v₁ :=
  by
  intros k 𝓦 v₀ v₁ τ Hsem_value
  cases τ
  case nat =>
    cases v₀ <;> try simp at Hsem_value
    case lit n₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lit n₁ =>
    constructor
    apply value.lit
    apply value.lit
  case unit =>
    cases v₀ <;> try simp at Hsem_value
    case unit =>
    cases v₁ <;> try simp at Hsem_value
    case unit =>
    constructor
    apply value.unit
    apply value.unit
  case arrow τ𝕒 τ𝕓 ε =>
    cases v₀ <;> try simp at Hsem_value
    case lam e₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lam e₁ =>
    cases ε <;> simp only [log_approx_value] at Hsem_value <;> try contradiction
    have ⟨Hwf₀, HG₀, Hwf₁, HG₁, Hsem_value⟩ := Hsem_value
    constructor
    apply value.lam; apply Hwf₀.left
    apply value.lam; apply Hwf₁.left
  case ref τ =>
    cases v₀ <;> try simp at Hsem_value
    case loc l₀ =>
    cases v₁ <;> try simp at Hsem_value
    case loc l₁ =>
    cases τ <;> simp only [log_approx_value] at Hsem_value <;> try contradiction
    constructor
    apply value.loc
    apply value.loc
  case fragment => simp at Hsem_value
  case rep => simp at Hsem_value

lemma log_approx_value.syntactic.wf :
  ∀ k 𝓦 v₀ v₁ τ,
    log_approx_value (k, 𝓦) v₀ v₁ τ →
    wf v₀ ∧ wf v₁ :=
  by
  intros k 𝓦 v₀ v₁ τ Hsem_value
  cases τ
  case nat =>
    cases v₀ <;> try simp at Hsem_value
    case lit n₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lit n₁ =>
    simp
  case arrow τ𝕒 τ𝕓 ε =>
    cases v₀ <;> try simp at Hsem_value
    case lam e₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lam e₁ =>
    cases ε <;> simp only [log_approx_value] at Hsem_value <;> try contradiction
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
    cases τ <;> simp only [log_approx_value] at Hsem_value <;> try contradiction
    simp
  case fragment => simp at Hsem_value
  case rep => simp at Hsem_value

lemma log_approx_value.syntactic.grounded :
  ∀ k 𝓦 v₀ v₁ τ,
    log_approx_value (k, 𝓦) v₀ v₁ τ →
    grounded v₀ ∧ grounded v₁ :=
  by
  intros k 𝓦 v₀ v₁ τ Hsem_value
  cases τ
  case nat =>
    cases v₀ <;> try simp at Hsem_value
    case lit n₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lit n₁ =>
    simp
  case arrow τ𝕒 τ𝕓 ε =>
    cases v₀ <;> try simp at Hsem_value
    case lam e₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lam e₁ =>
    cases ε <;> simp only [log_approx_value] at Hsem_value <;> try contradiction
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
    cases τ <;> simp only [log_approx_value] at Hsem_value <;> try contradiction
    simp
  case fragment => simp at Hsem_value
  case rep => simp at Hsem_value

lemma log_approx_value.apply :
  ∀ k 𝓦 f₀ arg₀ f₁ arg₁ τ𝕒 τ𝕓,
    log_approx_value (k, 𝓦) f₀ f₁ (.arrow τ𝕒 τ𝕓 ⊥) →
    log_approx_value (k, 𝓦) arg₀ arg₁ τ𝕒 →
    log_approx_expr (k, 𝓦) (.app₁ f₀ arg₀) (.app₁ f₁ arg₁) τ𝕓 :=
  by
  intros k 𝓦 f₀ arg₀ f₁ arg₁ τ𝕒 τ𝕓 Hsem_value_fun Hsem_value_arg
  cases f₀ <;> cases f₁ <;> simp only [log_approx_value] at Hsem_value_fun <;> try contradiction
  have ⟨_, _, _, _, Hsem_value_fun⟩ := Hsem_value_fun
  apply Hsem_value_fun
  constructor; omega; apply World.future.refl
  apply Hsem_value_arg

lemma log_approx_env.length :
  ∀ k 𝓦 γ₀ γ₁ Γ,
    log_approx_env (k, 𝓦) γ₀ γ₁ Γ →
    γ₀.length = Γ.length ∧
    γ₁.length = Γ.length :=
  by
  intros k 𝓦 γ₀ γ₁ Γ H
  generalize HEqi𝓦 : (k, 𝓦) = i𝓦
  rw [HEqi𝓦] at H
  induction H
  case nil => simp
  case cons IH =>
    constructor
    . simp; apply (IH HEqi𝓦).left
    . simp; apply (IH HEqi𝓦).right

lemma log_approx_env.binds_log_approx_value :
  ∀ k 𝓦 γ₀ γ₁ Γ x τ,
    log_approx_env (k, 𝓦) γ₀ γ₁ Γ →
    binds x (τ, 𝟚) Γ →
    log_approx_value (k, 𝓦) (msubst γ₀ (.fvar x)) (msubst γ₁ (.fvar x)) τ :=
  by
  intros k 𝓦 γ₀ γ₁ Γ x τ HsemΓ Hbinds
  generalize HEqi𝓦 : (k, 𝓦) = i𝓦
  rw [HEqi𝓦] at HsemΓ
  induction HsemΓ
  case nil => nomatch Hbinds
  case cons v₀ γ₀ v₁ γ₁ τ Γ Hsem_value HsemΓ IH =>
    have ⟨Hwf₀, Hwf₁⟩ := log_approx_value.syntactic.wf _ _ _ _ _ Hsem_value
    have ⟨HEq₀, HEq₁⟩ := log_approx_env.length _ _ _ _ _ HsemΓ
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
      apply IH; apply Hbinds; apply HEqi𝓦

lemma log_approx_env.syntactic.mwf :
  ∀ k 𝓦 γ₀ γ₁ Γ,
    log_approx_env (k, 𝓦) γ₀ γ₁ Γ →
    mwf γ₀ ∧ mwf γ₁ :=
  by
  intros k 𝓦 γ₀ γ₁ Γ HsemΓ
  generalize HEqi𝓦 : (k, 𝓦) = i𝓦
  rw [HEqi𝓦] at HsemΓ
  induction HsemΓ
  case nil => simp
  case cons v₀ γ₀ v₁ γ₁ τ Γ Hsem_value HsemΓ IH =>
    have ⟨IH₀, IH₁⟩ := IH HEqi𝓦
    have ⟨H₀, H₁⟩ := log_approx_value.syntactic.wf _ _ _ _ _ Hsem_value
    constructor
    . exact ⟨H₀, IH₀⟩
    . exact ⟨H₁, IH₁⟩

lemma log_approx_env.syntactic.mgrounded :
  ∀ k 𝓦 γ₀ γ₁ Γ,
    log_approx_env (k, 𝓦) γ₀ γ₁ Γ →
    mgrounded γ₀ ∧ mgrounded γ₁ :=
  by
  intros k 𝓦 γ₀ γ₁ Γ HsemΓ
  generalize HEqi𝓦 : (k, 𝓦) = i𝓦
  rw [HEqi𝓦] at HsemΓ
  induction HsemΓ
  case nil => simp
  case cons v₀ γ₀ v₁ γ₁ τ Γ Hsem_value HsemΓ IH =>
    have ⟨IH₀, IH₁⟩ := IH HEqi𝓦
    have ⟨H₀, H₁⟩ := log_approx_value.syntactic.grounded _ _ _ _ _ Hsem_value
    constructor
    . exact ⟨H₀, IH₀⟩
    . exact ⟨H₁, IH₁⟩
