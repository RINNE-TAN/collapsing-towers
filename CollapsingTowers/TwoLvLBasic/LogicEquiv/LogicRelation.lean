import CollapsingTowers.TwoLvLBasic.SyntacticTyping.Defs
import CollapsingTowers.TwoLvLBasic.Erasure.Defs

mutual
-- 𝓥⟦ℕ⟧ ≜ {(n, n) | n ∈ ℕ}
-- 𝓥⟦τ𝕒 → τ𝕓⟧ ≜ {(λ.e₀, λ.e₁) | ∀ (v₀, v₁) ∈ 𝓥⟦τ𝕒⟧. (e₀⟦0 ↦ v₀⟧, e₁⟦0 ↦ v₁⟧) ∈ 𝓔⟦τ𝕓⟧}
@[simp]
def logic_equiv_value : Expr → Expr → Ty → Prop
  | .lit n₀, .lit n₁, .nat => n₀ = n₁
  | .lam e₀, .lam e₁, (.arrow τ𝕒 τ𝕓 .pure) =>
      wf (.lam e₀) ∧
      wf (.lam e₁) ∧
      ∀ v₀ v₁,
        logic_equiv_value v₀ v₁ τ𝕒 →
        logic_equiv_expr (opening 0 v₀ e₀) (opening 0 v₁ e₁) τ𝕓
  | _, _, _ => false

-- 𝓔⟦τ⟧ ≜ {(e₀, e₁) | ∃v₀ v₁. e₀ ⇾* v₀ ∧ e₁ ⇾* v₁ ∧ (v₀, v₁) ∈ 𝓥⟦τ⟧}
@[simp]
def logic_equiv_expr (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
    ∃ v₀ v₁,
      (e₀ ⇾* v₀) ∧
      (e₁ ⇾* v₁) ∧
      logic_equiv_value v₀ v₁ τ
end

inductive logic_equiv_env : Subst → Subst → TEnv → Prop where
  | nil : logic_equiv_env [] [] []
  | cons :
    ∀ v₀ γ₀ v₁ γ₁ τ Γ,
      logic_equiv_value v₀ v₁ τ →
      logic_equiv_env γ₀ γ₁ Γ →
      logic_equiv_env (v₀ :: γ₀) (v₁ :: γ₁) ((τ, 𝟙) :: Γ)

-- Γ ⊧ e₀ ≈ e₁ : τ ≜ ∀ (γ₀, γ₁) ∈ 𝓖⟦Γ⟧. (γ₀(e₀), γ₁(e₁)) ∈ 𝓔⟦τ⟧
@[simp]
def logic_equiv_typing (Γ : TEnv) (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
  wf_at e₀ Γ.length ∧
  wf_at e₁ Γ.length ∧
  ∀ γ₀ γ₁,
    logic_equiv_env γ₀ γ₁ Γ →
    logic_equiv_expr (multi_subst γ₀ e₀) (multi_subst γ₁ e₁) τ

lemma logic_equiv_value.syntactic_value :
  ∀ v₀ v₁ τ,
    logic_equiv_value v₀ v₁ τ →
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
    have ⟨Hwf₀, Hwf₁, _⟩ := Hsem_value
    constructor
    apply value.lam; apply Hwf₀.left
    apply value.lam; apply Hwf₁.left
  all_goals simp at Hsem_value

lemma logic_equiv_value.wf :
  ∀ v₀ v₁ τ,
    logic_equiv_value v₀ v₁ τ →
    wf v₀ ∧
    wf v₁ :=
  by
  intros v₀ v₁ τ Hsem_value
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

lemma logic_equiv_env.multi_wf :
  ∀ γ₀ γ₁ Γ,
    logic_equiv_env γ₀ γ₁ Γ →
    multi_wf γ₀ ∧
    multi_wf γ₁ :=
  by
  intros γ₀ γ₁ Γ H
  induction H
  case nil => repeat constructor
  case cons Hsem_value _ IH =>
    constructor
    . constructor; apply And.left
      apply logic_equiv_value.wf
      apply Hsem_value; apply IH.left
    . constructor; apply And.right
      apply logic_equiv_value.wf
      apply Hsem_value; apply IH.right

lemma logic_equiv_env.length :
  ∀ γ₀ γ₁ Γ,
    logic_equiv_env γ₀ γ₁ Γ →
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

lemma logic_equiv_env.binds_logic_equiv_value :
  ∀ γ₀ γ₁ Γ x τ,
    logic_equiv_env γ₀ γ₁ Γ →
    binds x (τ, 𝟙) Γ →
    logic_equiv_value (multi_subst γ₀ (.fvar x)) (multi_subst γ₁ (.fvar x)) τ :=
  by
  intros γ₀ γ₁ Γ x τ HsemΓ Hbinds
  induction HsemΓ
  case nil => nomatch Hbinds
  case cons v₀ γ₀ v₁ γ₁ τ Γ Hsem_value HsemΓ IH =>
    have ⟨Hwf₀, Hwf₁⟩ := logic_equiv_value.wf _ _ _ Hsem_value
    have ⟨HEq₀, HEq₁⟩ := logic_equiv_env.length _ _ _ HsemΓ
    simp [HEq₀, HEq₁]
    by_cases HEqx : Γ.length = x
    . simp [if_pos HEqx]
      simp [if_pos HEqx] at Hbinds
      rw [← Hbinds, identity.multi_subst, identity.multi_subst]
      apply Hsem_value; apply Hwf₁.right; apply Hwf₀.right
    . simp [if_neg HEqx]
      simp [if_neg HEqx] at Hbinds
      apply IH; apply Hbinds

-- value v
-- —————————————
-- value γ₀(‖v‖)
--
--
-- value n  value λ.e        value (code x)  value (code e)
-- ———————  ———————————————  ——————————————  ——————————————————
-- value n  value λ.γ₀(‖e‖)  value γ₀(x)     Binding Time Error
lemma logic_equiv_env.erase_value :
  ∀ Γ v τ φ γ₀ γ₁,
    typing Γ 𝟙 v τ φ →
    logic_equiv_env γ₀ γ₁ ‖Γ‖𝛾 →
    value v →
    wbt 𝟙 τ →
    value (multi_subst γ₀ ‖v‖) ∧ value (multi_subst γ₁ ‖v‖) :=
  by
  intros Γ v τ φ γ₀ γ₁ Hτ HsemΓ Hvalue HwellBinds
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := logic_equiv_env.multi_wf _ _ _ HsemΓ
  cases Hvalue
  case lam Hlc =>
    simp
    constructor
    . apply value.lam
      apply lc.under_multi_subst; apply Hmulti_wf₀
      rw [← lc.under_erase]; apply Hlc
    . apply value.lam
      apply lc.under_multi_subst; apply Hmulti_wf₁
      rw [← lc.under_erase]; apply Hlc
  case lit =>
    simp; apply value.lit
  case code e _ =>
    cases e <;> cases Hτ <;> try simp at HwellBinds
    constructor
    . apply And.left; apply logic_equiv_value.syntactic_value
      apply logic_equiv_env.binds_logic_equiv_value
      apply HsemΓ; apply env.erase.binds; assumption
    . apply And.right; apply logic_equiv_value.syntactic_value
      apply logic_equiv_env.binds_logic_equiv_value
      apply HsemΓ; apply env.erase.binds; assumption

lemma logic_equiv_value.arrow_ty_iff_lam :
  ∀ f₀ f₁ τ𝕒 τ𝕓,
    logic_equiv_value f₀ f₁ (.arrow τ𝕒 τ𝕓 .pure) →
    ∃ e₀ e₁,
      f₀ = .lam e₀ ∧ f₁ = .lam e₁ :=
  by
  intros f₀ f₁ τ𝕒 τ𝕓 Hsem_value
  cases f₀ <;> cases f₁ <;> simp at Hsem_value
  simp

lemma logic_equiv_expr.stepn :
  ∀ e₀ e₁ r₀ r₁ τ,
    logic_equiv_expr r₀ r₁ τ →
    (e₀ ⇾* r₀) → (e₁ ⇾* r₁) →
    logic_equiv_expr e₀ e₁ τ :=
  by
  intros e₀ e₁ r₀ r₁ τ Hsem_expr Hstepr₀ Hstepr₁
  simp only [logic_equiv_expr] at *
  have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value⟩ := Hsem_expr
  exists v₀, v₁; constructor
  apply pure_stepn.trans; apply Hstepr₀; apply Hstepv₀; constructor
  apply pure_stepn.trans; apply Hstepr₁; apply Hstepv₁
  apply Hsem_value
