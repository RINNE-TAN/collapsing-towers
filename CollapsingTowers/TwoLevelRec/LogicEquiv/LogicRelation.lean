import CollapsingTowers.TwoLevelRec.SyntacticTyping.Defs

mutual
-- 𝓥⟦ℕ⟧ₖ ≜ {(n, n) | n ∈ ℕ}
-- 𝓥⟦τ𝕒 → τ𝕓⟧ₖ ≜ {(λ.e₀, λ.e₁) | ∀ j ≤ k, (v₀, v₁) ∈ 𝓥⟦τ𝕒⟧ⱼ. (λ.e₀ @ v₀, λ.e₁ @ v₁) ∈ 𝓔⟦τ𝕓⟧ⱼ}
@[simp]
def logic_rel_value : ℕ → Expr → Expr → Ty → Prop
  | _, .lit n₀, .lit n₁, .nat => n₀ = n₁
  | k, .lam e₀, .lam e₁, (.arrow τ𝕒 τ𝕓 .pure) =>
    wf (.lam e₀) ∧
    wf (.lam e₁) ∧
    ∀ j, j ≤ k →
      ∀ v₀ v₁,
        logic_rel_value j v₀ v₁ τ𝕒 →
        logic_rel_expr j (.app₁ (.lam e₀) v₀) (.app₁ (.lam e₁) v₁) τ𝕓
  | _, _, _, _ => false

termination_by k _ _ τ => (τ, k)
decreasing_by all_goals apply Prod.Lex.left; simp; omega

-- 𝓔⟦τ⟧ₖ ≜ {(e₀, e₁) | ∀ j < k, v₀. e₀ ⇾ⱼ v₀ → ∃ v₁, e₁ ⇾* v₁ ∧ (v₀, v₁) ∈ 𝓥⟦τ⟧ₖ₋ⱼ}
@[simp]
def logic_rel_expr (k : ℕ) (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
    ∀ j, j < k →
      ∀ v₀, value v₀ → (e₀ ⇾ ⟦j⟧ v₀) →
      ∃ v₁, (e₁ ⇾* v₁) ∧ logic_rel_value (k - j) v₀ v₁ τ

termination_by (τ, k + 1)
decreasing_by apply Prod.Lex.right; omega
end

inductive logic_rel_env : ℕ → Subst → Subst → TEnv → Prop where
  | nil : ∀ k, logic_rel_env k [] [] []
  | cons :
    ∀ k v₀ γ₀ v₁ γ₁ τ Γ,
      logic_rel_value k v₀ v₁ τ →
      logic_rel_env k γ₀ γ₁ Γ →
      logic_rel_env k (v₀ :: γ₀) (v₁ :: γ₁) ((τ, 𝟙) :: Γ)

-- Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ ≜ ∀ k ≥ 0, (γ₀, γ₁) ∈ 𝓖⟦Γ⟧ₖ. (γ₀(e₀), γ₁(e₁)) ∈ 𝓔⟦τ⟧ₖ
@[simp]
def logic_rel_typing (Γ : TEnv) (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
  wf_at e₀ Γ.length ∧
  wf_at e₁ Γ.length ∧
  ∀ k γ₀ γ₁,
    logic_rel_env k γ₀ γ₁ Γ →
    logic_rel_expr k (multi_subst γ₀ e₀) (multi_subst γ₁ e₁) τ

-- Γ ⊧ e₀ ≈𝑙𝑜𝑔 e₁ : τ ≜ Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ ∧ Γ ⊧ e₁ ≤𝑙𝑜𝑔 e₀ : τ
@[simp]
def logic_equiv (Γ : TEnv) (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
  logic_rel_typing Γ e₀ e₁ τ ∧ logic_rel_typing Γ e₁ e₀ τ

lemma logic_rel_value.weakening :
  ∀ k₀ k₁ v₀ v₁ τ,
    logic_rel_value k₀ v₀ v₁ τ →
    k₁ ≤ k₀ →
    logic_rel_value k₁ v₀ v₁ τ :=
  by
  intros k₀ k₁ v₀ v₁ τ Hsem_value HLe
  cases τ
  case nat =>
    cases v₀ <;> cases v₁ <;> simp at *
    omega
  case arrow τ𝕒 τ𝕓 φ =>
    cases v₀ <;> try simp at Hsem_value
    case lam e₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lam e₁ =>
    cases φ
    case reify => simp at Hsem_value
    case pure =>
      simp only [logic_rel_value] at Hsem_value
      have ⟨Hwf₀, Hwf₁, Hsem_value_lam⟩ := Hsem_value
      simp only [logic_rel_value]
      constructor; apply Hwf₀
      constructor; apply Hwf₁
      intros j HLe; apply Hsem_value_lam; omega
  case fragment => simp at Hsem_value
  case rep => simp at Hsem_value

lemma logic_rel_expr.weakening :
  ∀ k₀ k₁ e₀ e₁ τ,
    logic_rel_expr k₀ e₀ e₁ τ →
    k₁ ≤ k₀ →
    logic_rel_expr k₁ e₀ e₁ τ :=
  by
  intros k₀ k₁ e₀ e₁ τ Hsem_expr HLe
  simp only [logic_rel_expr]
  simp only [logic_rel_expr] at Hsem_expr
  intros j Hindex v₀ Hvalue₀ Hstep₀
  have ⟨v₁, Hstep₁, Hsem_value⟩ := Hsem_expr j (by omega) v₀ Hvalue₀ Hstep₀
  exists v₁
  constructor; apply Hstep₁
  apply logic_rel_value.weakening
  apply Hsem_value; omega

lemma logic_rel_env.weakening :
  ∀ k₀ k₁ γ₀ γ₁ Γ,
    logic_rel_env k₀ γ₀ γ₁ Γ →
    k₁ ≤ k₀ →
    logic_rel_env k₁ γ₀ γ₁ Γ :=
  by
  intros k₀ k₁ γ₀ γ₁ Γ HsemΓ HLe
  induction HsemΓ
  case nil => apply logic_rel_env.nil
  case cons Hsem_value _ IH =>
    apply logic_rel_env.cons
    apply logic_rel_value.weakening; apply Hsem_value; apply HLe
    apply IH

lemma logic_rel_value.syntactic_value :
  ∀ k v₀ v₁ τ,
    logic_rel_value k v₀ v₁ τ →
    value v₀ ∧ value v₁ :=
  by
  intros k v₀ v₁ τ Hsem_value
  cases τ
  case nat =>
    cases v₀ <;> cases v₁ <;> simp at Hsem_value
    constructor
    apply value.lit
    apply value.lit
  case arrow φ =>
    cases v₀ <;> cases v₁ <;> cases φ <;> simp at Hsem_value
    have ⟨Hwf₀, Hwf₁, _⟩ := Hsem_value
    constructor
    apply value.lam; apply Hwf₀.left
    apply value.lam; apply Hwf₁.left
  all_goals simp at Hsem_value

lemma logic_rel_value.wf :
  ∀ k v₀ v₁ τ,
    logic_rel_value k v₀ v₁ τ →
    wf v₀ ∧ wf v₁ :=
  by
  intros k v₀ v₁ τ Hsem_value
  cases τ
  case nat =>
    cases v₀ <;> cases v₁ <;> simp at Hsem_value
    repeat constructor
  case arrow φ =>
    cases v₀ <;> cases v₁ <;> cases φ <;> simp at Hsem_value
    have ⟨Hwf₀, Hwf₁, _⟩ := Hsem_value
    constructor
    apply Hwf₀; apply Hwf₁
  all_goals simp at Hsem_value

lemma logic_rel_value.arrow_ty_iff_lam :
  ∀ k f₀ f₁ τ𝕒 τ𝕓,
    logic_rel_value k f₀ f₁ (.arrow τ𝕒 τ𝕓 .pure) →
    ∃ e₀ e₁,
      f₀ = .lam e₀ ∧ f₁ = .lam e₁ :=
  by
  intros k f₀ f₁ τ𝕒 τ𝕓 Hsem_value
  cases f₀ <;> cases f₁ <;> simp at Hsem_value
  simp

lemma logic_rel_value.apply :
  ∀ k f₀ arg₀ f₁ arg₁ τ𝕒 τ𝕓,
    logic_rel_value k f₀ f₁ (.arrow τ𝕒 τ𝕓 ∅) →
    logic_rel_value k arg₀ arg₁ τ𝕒 →
    logic_rel_expr k (.app₁ f₀ arg₀) (.app₁ f₁ arg₁) τ𝕓 :=
  by
  intros k f₀ arg₀ f₁ arg₁ τ𝕒 τ𝕓 Hsem_value_fun Hsem_value_arg
  have ⟨e₀, e₁, HEq₀, HEq₁⟩ := logic_rel_value.arrow_ty_iff_lam _ f₀ f₁ _ _ Hsem_value_fun
  rw [HEq₀, HEq₁]
  rw [HEq₀, HEq₁] at Hsem_value_fun
  simp only [logic_rel_value] at Hsem_value_fun
  have ⟨Hwf₀, Hwf₁, Hsem_value_fun⟩ := Hsem_value_fun
  apply Hsem_value_fun; rfl; apply Hsem_value_arg

lemma logic_rel_env.length :
  ∀ k γ₀ γ₁ Γ,
    logic_rel_env k γ₀ γ₁ Γ →
    γ₀.length = Γ.length ∧
    γ₁.length = Γ.length :=
  by
  intros k γ₀ γ₁ Γ H
  induction H
  case nil => simp
  case cons IH =>
    constructor
    . simp; apply IH.left
    . simp; apply IH.right

lemma logic_rel_env.binds_logic_rel_value :
  ∀ k γ₀ γ₁ Γ x τ,
    logic_rel_env k γ₀ γ₁ Γ →
    binds x (τ, 𝟙) Γ →
    logic_rel_value k (multi_subst γ₀ (.fvar x)) (multi_subst γ₁ (.fvar x)) τ :=
  by
  intros k γ₀ γ₁ Γ x τ HsemΓ Hbinds
  induction HsemΓ
  case nil => nomatch Hbinds
  case cons v₀ γ₀ v₁ γ₁ τ Γ Hsem_value HsemΓ IH =>
    have ⟨Hwf₀, Hwf₁⟩ := logic_rel_value.wf _ _ _ _ Hsem_value
    have ⟨HEq₀, HEq₁⟩ := logic_rel_env.length _ _ _ _ HsemΓ
    simp [HEq₀, HEq₁]
    by_cases HEqx : Γ.length = x
    . simp [if_pos HEqx]
      simp [if_pos HEqx] at Hbinds
      rw [← Hbinds, identity.multi_subst, identity.multi_subst]
      apply Hsem_value; apply Hwf₁.right; apply Hwf₀.right
    . simp [if_neg HEqx]
      simp [if_neg HEqx] at Hbinds
      apply IH; apply Hbinds

lemma logic_rel_env.multi_wf :
  ∀ k γ₀ γ₁ Γ,
    logic_rel_env k γ₀ γ₁ Γ →
    multi_wf γ₀ ∧ multi_wf γ₁ :=
  by
  intros k γ₀ γ₁ Γ H
  induction H
  case nil => repeat constructor
  case cons Hsem_value _ IH =>
    constructor
    . constructor; apply And.left
      apply logic_rel_value.wf
      apply Hsem_value; apply IH.left
    . constructor; apply And.right
      apply logic_rel_value.wf
      apply Hsem_value; apply IH.right

lemma logic_rel_expr.stepn :
  ∀ k i e₀ e₁ r₀ r₁ τ,
    logic_rel_expr (k - i) r₀ r₁ τ →
    (e₀ ⇾ ⟦i⟧ r₀) → (e₁ ⇾* r₁) →
    logic_rel_expr k e₀ e₁ τ :=
  by
  intros k i e₀ e₁ r₀ r₁ τ Hsem_expr Hstepe₀ Hstepe₁
  simp only [logic_rel_expr] at *
  intros j Hindexj v₀ Hvalue₀ Hstep₀
  have ⟨jl, jr, v, HEqIndex, Hstepv₀, Hstepr₀⟩ := pure_stepn_indexed.church_rosser _ _ _ _ _ Hstep₀ Hstepe₀
  have ⟨HEqv, Hj⟩ := pure_stepn_indexed.value_impl_termination _ _ _ Hvalue₀ Hstepv₀
  rw [← HEqv] at Hstepr₀
  rw [Hj] at HEqIndex
  have ⟨v₁, Hstepr₁, Hsem_value⟩ := Hsem_expr jr (by omega) _ Hvalue₀ Hstepr₀
  exists v₁
  constructor; apply pure_stepn.trans; apply Hstepe₁; apply Hstepr₁
  have HEqIndex : k - j = k - i - jr := by omega
  rw [HEqIndex]; apply Hsem_value
