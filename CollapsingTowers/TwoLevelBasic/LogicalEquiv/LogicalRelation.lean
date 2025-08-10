import CollapsingTowers.TwoLevelBasic.SyntacticTyping.Defs
import CollapsingTowers.TwoLevelBasic.Erasure.Defs

mutual
-- 𝓥⟦ℕ⟧ ≜ {(n, n) | n ∈ ℕ}
-- 𝓥⟦τ𝕒 → τ𝕓⟧ ≜ {(λ.e₀, λ.e₁) | ∀ (v₀, v₁) ∈ 𝓥⟦τ𝕒⟧. (e₀⟦0 ↦ v₀⟧, e₁⟦0 ↦ v₁⟧) ∈ 𝓔⟦τ𝕓⟧}
@[simp]
def log_equiv_value : Expr → Expr → Ty → Prop
  | .lit n₀, .lit n₁, .nat => n₀ = n₁
  | .lam e₀, .lam e₁, (.arrow τ𝕒 τ𝕓 .pure) =>
      wf (.lam e₀) ∧
      wf (.lam e₁) ∧
      ∀ v₀ v₁,
        log_equiv_value v₀ v₁ τ𝕒 →
        log_equiv_expr (opening 0 v₀ e₀) (opening 0 v₁ e₁) τ𝕓
  | _, _, _ => false

-- 𝓔⟦τ⟧ ≜ {(e₀, e₁) | ∃v₀ v₁. e₀ ⇾* v₀ ∧ e₁ ⇾* v₁ ∧ (v₀, v₁) ∈ 𝓥⟦τ⟧}
@[simp]
def log_equiv_expr (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
    ∃ v₀ v₁,
      (e₀ ⇾* v₀) ∧
      (e₁ ⇾* v₁) ∧
      log_equiv_value v₀ v₁ τ
end

inductive log_equiv_env : Subst → Subst → TEnv → Prop where
  | nil : log_equiv_env [] [] []
  | cons :
    ∀ v₀ γ₀ v₁ γ₁ τ Γ,
      log_equiv_value v₀ v₁ τ →
      log_equiv_env γ₀ γ₁ Γ →
      log_equiv_env (v₀ :: γ₀) (v₁ :: γ₁) ((τ, 𝟙) :: Γ)

-- Γ ⊧ e₀ ≈ e₁ : τ ≜ ∀ (γ₀, γ₁) ∈ 𝓖⟦Γ⟧. (γ₀(e₀), γ₁(e₁)) ∈ 𝓔⟦τ⟧
@[simp]
def log_equiv_typing (Γ : TEnv) (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
  wf_at e₀ Γ.length ∧
  wf_at e₁ Γ.length ∧
  ∀ γ₀ γ₁,
    log_equiv_env γ₀ γ₁ Γ →
    log_equiv_expr (multi_subst γ₀ e₀) (multi_subst γ₁ e₁) τ

lemma log_equiv_value.syntactic_value :
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
    have ⟨Hwf₀, Hwf₁, _⟩ := Hsem_value
    constructor
    apply value.lam; apply Hwf₀.left
    apply value.lam; apply Hwf₁.left
  all_goals simp at Hsem_value

lemma log_equiv_value.wf :
  ∀ v₀ v₁ τ,
    log_equiv_value v₀ v₁ τ →
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

lemma log_equiv_env.multi_wf :
  ∀ γ₀ γ₁ Γ,
    log_equiv_env γ₀ γ₁ Γ →
    multi_wf γ₀ ∧
    multi_wf γ₁ :=
  by
  intros γ₀ γ₁ Γ H
  induction H
  case nil => repeat constructor
  case cons Hsem_value _ IH =>
    constructor
    . constructor; apply And.left
      apply log_equiv_value.wf
      apply Hsem_value; apply IH.left
    . constructor; apply And.right
      apply log_equiv_value.wf
      apply Hsem_value; apply IH.right

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
    binds x (τ, 𝟙) Γ →
    log_equiv_value (multi_subst γ₀ (.fvar x)) (multi_subst γ₁ (.fvar x)) τ :=
  by
  intros γ₀ γ₁ Γ x τ HsemΓ Hbinds
  induction HsemΓ
  case nil => nomatch Hbinds
  case cons v₀ γ₀ v₁ γ₁ τ Γ Hsem_value HsemΓ IH =>
    have ⟨Hwf₀, Hwf₁⟩ := log_equiv_value.wf _ _ _ Hsem_value
    have ⟨HEq₀, HEq₁⟩ := log_equiv_env.length _ _ _ HsemΓ
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
lemma log_equiv_env.erase_value :
  ∀ Γ v τ φ γ₀ γ₁,
    typing Γ 𝟙 v τ φ →
    log_equiv_env γ₀ γ₁ ‖Γ‖𝛾 →
    value v →
    wbt 𝟙 τ →
    value (multi_subst γ₀ ‖v‖) ∧ value (multi_subst γ₁ ‖v‖) :=
  by
  intros Γ v τ φ γ₀ γ₁ Hτ HsemΓ Hvalue HwellBinds
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := log_equiv_env.multi_wf _ _ _ HsemΓ
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
    . apply And.left; apply log_equiv_value.syntactic_value
      apply log_equiv_env.binds_log_equiv_value
      apply HsemΓ; apply env.erase.binds; assumption
    . apply And.right; apply log_equiv_value.syntactic_value
      apply log_equiv_env.binds_log_equiv_value
      apply HsemΓ; apply env.erase.binds; assumption

lemma log_equiv_env.erase_ctx𝔼 :
  ∀ E₀ Γ e τ φ γ₀ γ₁,
    ctx𝔼 E₀ →
    typing Γ 𝟙 E₀⟦e⟧ τ φ →
    log_equiv_env γ₀ γ₁ ‖Γ‖𝛾 →
    ∃ E₁, ctx𝔼 E₁ ∧ closed_at E₁⟦e⟧ Γ.length ∧ (∀ e, multi_subst γ₀ ‖E₀⟦e⟧‖ = E₁⟦multi_subst γ₀ ‖e‖⟧) :=
  by
  intros E₀ Γ e τ φ γ₀ γ₁ HE₀ Hτ HsemΓ
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := log_equiv_env.multi_wf _ _ _ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := log_equiv_env.length _ _ _ HsemΓ
  induction HE₀ generalizing τ φ
  case hole =>
    exists id
    constructor; apply ctx𝔼.hole
    constructor; apply typing.closed_at_env; apply Hτ
    intro e; rfl
  case cons𝔹 HB HE IH =>
    cases HB
    case appl₁ arg Hlc =>
      cases Hτ
      case app₁ Harg HX =>
        have ⟨E, HE, HcloseE, IHγ⟩ := IH _ _ HX
        exists (fun X => .app₁ X (multi_subst γ₀ ‖arg‖)) ∘ E
        constructor
        apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appl₁ _ _) HE
        apply lc.under_multi_subst; apply Hmulti_wf₀; rw [← lc.under_erase]; apply Hlc
        constructor
        constructor
        . apply HcloseE
        . apply closed.inc
          apply closed.under_multi_subst; apply Hmulti_wf₀
          rw [← closed.under_erase]
          rw [HEq₀, ← env.erase.length]
          apply typing.closed_at_env; apply Harg; omega
        simp; apply IHγ
    case appr₁ f Hvalue =>
      cases Hτ
      case app₁ HX Hf =>
        cases Hvalue with
        | lam e Hlc =>
        have ⟨E, HE, HcloseE, IHγ⟩ := IH _ _ HX
        exists (fun X => .app₁ (multi_subst γ₀ (‖.lam e‖)) X) ∘ E
        constructor
        apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appr₁ _ _) HE
        simp; apply value.lam
        apply lc.under_multi_subst; apply Hmulti_wf₀
        rw [← lc.under_erase]; apply Hlc
        constructor
        constructor
        . apply closed.inc
          apply closed.under_multi_subst; apply Hmulti_wf₀
          rw [← closed.under_erase]
          rw [HEq₀, ← env.erase.length]
          apply typing.closed_at_env; apply Hf; omega
        . apply HcloseE
        simp; apply IHγ
        | _ => cases Hf
    case appl₂ arg Hlc =>
      cases Hτ
      case app₂ HX Harg =>
        have ⟨E, HE, HcloseE, IHγ⟩ := IH _ _ HX
        exists (fun X => .app₁ X (multi_subst γ₀ ‖arg‖)) ∘ E
        constructor
        apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appl₁ _ _) HE
        apply lc.under_multi_subst; apply Hmulti_wf₀; rw [← lc.under_erase]; apply Hlc
        constructor
        constructor
        . apply HcloseE
        . apply closed.inc
          apply closed.under_multi_subst; apply Hmulti_wf₀
          rw [← closed.under_erase]
          rw [HEq₀, ← env.erase.length]
          apply typing.closed_at_env; apply Harg; omega
        simp; apply IHγ
    case appr₂ f Hvalue =>
      cases Hτ
      case app₂ Hf HX =>
        cases Hvalue with
        | code e Hlc =>
          cases Hf with
          | code_fragment _ x _ Hbinds =>
            have ⟨E, HE, HcloseE, IHγ⟩ := IH _ _ HX
            exists (fun X => .app₁ (multi_subst γ₀ (‖.code (.fvar x)‖)) X) ∘ E
            constructor
            apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appr₁ _ _) HE
            apply And.left; apply log_equiv_value.syntactic_value
            apply log_equiv_env.binds_log_equiv_value
            apply HsemΓ; apply env.erase.binds; assumption
            constructor
            constructor
            . apply closed.inc
              apply closed.under_multi_subst; apply Hmulti_wf₀
              rw [← closed.under_erase]
              simp [HEq₀, ← env.erase.length]
              rw [getr_exists_iff_index_lt_length]; constructor; apply Hbinds
              omega
            . apply HcloseE
            simp; apply IHγ
        | _ => cases Hf
    case lift =>
      cases Hτ
      case lift_lam HX =>
        have ⟨E, HE, HcloseE, IHγ⟩ := IH _ _ HX
        exists E
      case lift_lit HX =>
        have ⟨E, HE, HcloseE, IHγ⟩ := IH _ _ HX
        exists E
    case lets e Hlc =>
      cases Hτ
      case lets HX Hclose He =>
        have ⟨E, HE, HcloseE, IHγ⟩ := IH _ _ HX
        exists (fun X => .lets X (multi_subst γ₀ ‖e‖)) ∘ E
        constructor
        apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.lets _ _) HE
        apply lc.under_multi_subst; apply Hmulti_wf₀; rw [← lc.under_erase]; apply Hlc
        constructor
        constructor
        . apply HcloseE
        . apply closed.inc
          apply closed.under_multi_subst; apply Hmulti_wf₀
          rw [← closed.under_erase]
          rw [HEq₀, ← env.erase.length]; apply Hclose; omega
        simp; apply IHγ

lemma log_equiv_value.arrow_ty_iff_lam :
  ∀ f₀ f₁ τ𝕒 τ𝕓,
    log_equiv_value f₀ f₁ (.arrow τ𝕒 τ𝕓 .pure) →
    ∃ e₀ e₁,
      f₀ = .lam e₀ ∧ f₁ = .lam e₁ :=
  by
  intros f₀ f₁ τ𝕒 τ𝕓 Hsem_value
  cases f₀ <;> cases f₁ <;> simp at Hsem_value
  simp

lemma log_equiv_expr.stepn :
  ∀ e₀ e₁ r₀ r₁ τ,
    log_equiv_expr r₀ r₁ τ →
    (e₀ ⇾* r₀) → (e₁ ⇾* r₁) →
    log_equiv_expr e₀ e₁ τ :=
  by
  intros e₀ e₁ r₀ r₁ τ Hsem_expr Hstepr₀ Hstepr₁
  simp only [log_equiv_expr] at *
  have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value⟩ := Hsem_expr
  exists v₀, v₁; constructor
  apply pure_stepn.trans; apply Hstepr₀; apply Hstepv₀; constructor
  apply pure_stepn.trans; apply Hstepr₁; apply Hstepv₁
  apply Hsem_value
