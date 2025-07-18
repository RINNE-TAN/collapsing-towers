
import CollapsingTowers.TwoLevelBasic.SemEquiv.Fundamental
import CollapsingTowers.TwoLevelBasic.Preservation.Defs
theorem multi_subst_erase_value :
  ∀ Γ v τ φ γ₀ γ₁,
    typing Γ .stat v τ φ →
    sem_equiv_env γ₀ γ₁ (erase_env Γ) →
    value v →
    well_binding_time .stat τ →
    value (multi_subst γ₀ (erase v)) ∧ value (multi_subst γ₁ (erase v)) :=
  by
  intros Γ v τ φ γ₀ γ₁ Hτ HsemΓ Hvalue HwellBinds
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := sem_equiv_env_impl_multi_wf _ _ _ HsemΓ
  cases Hvalue
  case lam Hlc =>
    simp
    constructor
    . apply value.lam
      apply multi_subst_lc_at; apply Hmulti_wf₀
      rw [← erase_lc_at]; apply Hlc
    . apply value.lam
      apply multi_subst_lc_at; apply Hmulti_wf₁
      rw [← erase_lc_at]; apply Hlc
  case lit =>
    simp; apply value.lit
  case code e _ =>
    cases e <;> cases Hτ <;> try simp at HwellBinds
    constructor
    . apply And.left; apply sem_equiv_value_impl_value
      apply sem_equiv_env_impl_sem_equiv_value
      apply HsemΓ; apply binds_erase_env; assumption
    . apply And.right; apply sem_equiv_value_impl_value
      apply sem_equiv_env_impl_sem_equiv_value
      apply HsemΓ; apply binds_erase_env; assumption

theorem sem_preservation_head :
  ∀ Γ e₀ e₁ τ φ,
    head𝕄 e₀ e₁ →
    typing Γ .stat e₀ τ φ →
    typing Γ .stat e₁ τ φ →
    sem_equiv_typing (erase_env Γ) (erase e₀) (erase e₁) (erase_ty τ) :=
  by
  intros Γ e₀ e₁ τ φ Hhead Hτ₀ Hτ₁
  cases Hhead <;> try apply fundamental; apply Hτ₀
  case lets Hvalue =>
    constructor; constructor
    . rw [lc, ← erase_lc_at]; apply typing_regular; apply Hτ₀
    . rw [← length_erase_env, ← erase_closed_at]
      apply typing_closed; apply Hτ₀
    constructor; constructor
    . rw [lc, ← erase_lc_at]; apply typing_regular; apply Hτ₁
    . rw [← length_erase_env, ← erase_closed_at]
      apply typing_closed; apply Hτ₁
    intros γ₀ γ₁ HsemΓ
    have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := sem_equiv_env_impl_multi_wf _ _ _ HsemΓ
    apply sem_equiv_expr_stepn
    apply (fundamental _ _ _ _ _ Hτ₁).right.right; apply HsemΓ
    . apply pure_stepn.multi; apply pure_stepn.refl
      rw [erase_open_subst_comm, multi_subst_open_subst_comm _ _ _ Hmulti_wf₀]
      apply pure_step.pure_step𝕄 id; apply ctx𝕄.hole
      apply multi_subst_lc_at; apply Hmulti_wf₀; rw [← erase_lc_at]; apply typing_regular; apply Hτ₀
      simp; apply head𝕄.lets
      cases Hτ₀ with
      | lets _ _ _ _ _ _ _ _ Hτv _ HwellBinds _ =>
          apply And.left; apply multi_subst_erase_value
          apply Hτv; apply HsemΓ; apply Hvalue; apply HwellBinds
    . apply pure_stepn.refl
  case app₁ Hvalue =>
    --
    --
    -- value v
    -- ——————————————————————————————————
    -- |Γ| ⊧ |λ.e @ v| ≈ |e⟦0 ↦ v⟧| : |τ|
    --
    --
    -- value v
    -- (γ₀, γ₁) ∈ 𝓖⟦Γ⟧
    -- ————————————————————————————————————————
    -- (γ₀(|λ.e @ v|), γ₁(|e⟦0 ↦ v⟧|)) ∈ 𝓔⟦|τ|⟧
    --
    --
    -- value v
    -- (γ₀, γ₁) ∈ 𝓖⟦Γ⟧
    -- ————————————————————————————————————————————————————
    -- (λ.γ₀(|e|) @ γ₀(|v|), γ₁(|e|)⟦0 ↦ γ₁(|v|)⟧) ∈ 𝓔⟦|τ|⟧
    --
    --
    -- value v
    -- ————————————————————————————————————————————
    -- λ.γ₀(|e|) @ γ₀(|v|) ↦* γ₁(|e|)⟦0 ↦ γ₁(|v|)⟧
    --
    --
    -- value v
    -- —————————————
    -- value γ₀(|v|)
    --
    --
    -- value n  value λ.e        value (code x)  value (code e)
    -- ———————  ———————————————  ——————————————  ——————————————————
    -- value n  value λ.γ₀(|e|)  value γ₀(x)     Binding Time Error
    constructor; constructor
    . rw [lc, ← erase_lc_at]; apply typing_regular; apply Hτ₀
    . rw [← length_erase_env, ← erase_closed_at]
      apply typing_closed; apply Hτ₀
    constructor; constructor
    . rw [lc, ← erase_lc_at]; apply typing_regular; apply Hτ₁
    . rw [← length_erase_env, ← erase_closed_at]
      apply typing_closed; apply Hτ₁
    intros γ₀ γ₁ HsemΓ
    have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := sem_equiv_env_impl_multi_wf _ _ _ HsemΓ
    apply sem_equiv_expr_stepn
    apply (fundamental _ _ _ _ _ Hτ₁).right.right; apply HsemΓ
    . apply pure_stepn.multi; apply pure_stepn.refl
      rw [erase_open_subst_comm, multi_subst_open_subst_comm _ _ _ Hmulti_wf₀]
      apply pure_step.pure_step𝕄 id; apply ctx𝕄.hole
      apply multi_subst_lc_at; apply Hmulti_wf₀; rw [← erase_lc_at]; apply typing_regular; apply Hτ₀
      simp; apply head𝕄.app₁
      cases Hτ₀ with
      | app₁ _ _ _ _ _ _ _ _ _ Hτe Hτv =>
        cases Hτe with
        | lam _ _ _ _ _ _ _ HwellBinds =>
          apply And.left; apply multi_subst_erase_value
          apply Hτv; apply HsemΓ; apply Hvalue; apply HwellBinds
    . apply pure_stepn.refl
  case lift_lam e =>
    have HEq : erase (.lam𝕔 (map𝕔₀ e)) = erase (.lift (.lam e)) :=
      by simp [erase_maping𝕔]
    rw [HEq]; apply fundamental; apply Hτ₀

-- Γ ⊢ e₀ : τ →
-- |Γ| ⊨ |e₀| ≈ |e₁| : |τ|
-- ————————————————————————————
-- Γ ⊢ B⟦e₀⟧ : τ →
-- |Γ| ⊨ |B⟦e₀⟧| ≈ |B⟦e₁⟧| : |τ|
theorem sem_decompose𝔹 :
  ∀ Γ B e₀ e₁ τ φ,
    ctx𝔹 B →
    (∀ τ φ,
      typing Γ .stat e₀ τ φ →
      sem_equiv_typing (erase_env Γ) (erase e₀) (erase e₁) (erase_ty τ)
    ) →
    typing Γ .stat B⟦e₀⟧ τ φ →
    sem_equiv_typing (erase_env Γ) (erase B⟦e₀⟧) (erase B⟦e₁⟧) (erase_ty τ) :=
  by
  intros Γ B e₀ e₁ τ φ HB IH Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ τ𝕒 _ _ _ Harg HX =>
      apply compatibility_app
      apply IH (.arrow τ𝕒 τ _); apply HX
      apply fundamental; apply Harg
  case appr₁ =>
    cases Hτ
    case app₁ τ𝕒 _ _ _ HX Hf =>
      apply compatibility_app
      apply fundamental _ _ _ (.arrow τ𝕒 τ _); apply Hf
      apply IH; apply HX
  case appl₂ =>
    cases Hτ
    case app₂ τ𝕒 τ𝕓 _ _ HX Harg =>
      apply compatibility_app
      apply IH (.fragment (.arrow τ𝕒 τ𝕓 _)); apply HX
      apply fundamental _ _ _ (.fragment τ𝕒); apply Harg
  case appr₂ =>
    cases Hτ
    case app₂ τ𝕒 τ𝕓 _ _ Hf HX =>
      apply compatibility_app
      apply fundamental _ _ _ (.fragment (.arrow τ𝕒 τ𝕓 _)); apply Hf
      apply IH (.fragment τ𝕒); apply HX
  case lift =>
    cases Hτ
    case lift_lam τ𝕒 τ𝕓 _ _ HX =>
      apply IH (.arrow (.fragment τ𝕒) (.fragment τ𝕓) _); apply HX
    case lift_lit HX =>
      apply IH .nat; apply HX
  case lets Hlc =>
    cases Hτ
    case lets HX Hclose He =>
      have Hsem := IH _ _ HX
      have ⟨Hwf₀, Hwf₁, _⟩ := Hsem
      apply compatibility_lets
      constructor
      . apply Hwf₀.right
      . rw [← length_erase_env, ← erase_closed_at]; apply Hclose
      constructor
      . apply Hwf₁.right
      . rw [← length_erase_env, ← erase_closed_at]; apply Hclose
      apply Hsem
      rw [← erase_env, ← erase_open₀_comm]; apply fundamental
      rw [← length_erase_env]; apply He

-- Γ ⊢ e₀ : τ →
-- |Γ| ⊨ |e₀| ≈ |e₁| : |τ|
-- ————————————————————————————
-- Γ ⊢ R⟦e₀⟧ : τ →
-- |Γ| ⊨ |R⟦e₀⟧| ≈ |R⟦e₁⟧| : |τ|
theorem sem_decomposeℝ :
  ∀ intro Γ R e₀ e₁ τ φ,
    ctxℝ intro Γ.length R →
    lc e₀ →
    (∀ Δ τ φ,
      Δ.length = intro →
      typing (Δ ++ Γ) .stat e₀ τ φ →
      sem_equiv_typing (erase_env (Δ ++ Γ)) (erase e₀) (erase e₁) (erase_ty τ)
    ) →
    typing Γ .stat R⟦e₀⟧ τ φ →
    sem_equiv_typing (erase_env Γ) (erase R⟦e₀⟧) (erase R⟦e₁⟧) (erase_ty τ) :=
  by
  intros intro Γ R e₀ e₁ τ φ HR Hlc IH Hτ
  cases HR
  case lam𝕔 =>
    cases Hτ
    case lam𝕔 _ _ _ _ Hτ Hclose =>
      cases Hτ
      all_goals
      next Hτ =>
        rw [← List.singleton_append, open_close_id₀ _ _ Hlc] at Hτ
        have Hsem := IH _ _ _ (by simp) Hτ
        have ⟨Hwf₀, Hwf₁, _⟩ := Hsem
        apply compatibility_lam
        . simp [← length_erase_env, ← erase_closed_at]; apply Hclose
        . simp [← length_erase_env, ← erase_closed_at, ← close_closed]
          rw [← length_erase_env] at Hwf₁
          rw [erase_closed_at]; apply Hwf₁.right
        rw [← erase_open₀_comm, ← erase_open₀_comm]
        rw [← length_erase_env, open_close_id₀, open_close_id₀]
        apply Hsem
        . rw [lc, erase_lc_at]; apply Hwf₁.left
        . apply Hlc
  case let𝕔 =>
    cases Hτ
    case let𝕔 Hτb Hτe Hclose =>
      cases Hτe
      all_goals
      next Hτe =>
        rw [← List.singleton_append, open_close_id₀ _ _ Hlc] at Hτe
        have Hsem := IH _ _ _ (by simp) Hτe
        have ⟨Hwf₀, Hwf₁, _⟩ := Hsem
        apply compatibility_lets
        constructor
        . simp [← length_erase_env, ← erase_closed_at]; apply typing_closed; apply Hτb
        . simp [← length_erase_env, ← erase_closed_at]; apply Hclose
        constructor
        . simp [← length_erase_env, ← erase_closed_at]; apply typing_closed; apply Hτb
        . simp [← length_erase_env, ← erase_closed_at, ← close_closed]
          rw [← length_erase_env] at Hwf₁
          rw [erase_closed_at]; apply Hwf₁.right
        apply fundamental; apply Hτb
        rw [← erase_open₀_comm, ← erase_open₀_comm]
        rw [← length_erase_env, open_close_id₀, open_close_id₀]
        apply Hsem
        . rw [lc, erase_lc_at]; apply Hwf₁.left
        . apply Hlc
  case run =>
    cases Hτ
    case run Hτ =>
      cases Hτ
      case pure Hτ =>
        apply IH [] (.rep τ)
        simp; apply Hτ
      case reify Hτ =>
        apply IH [] (.fragment τ)
        simp; apply Hτ

theorem sem_decompose𝔼 :
  ∀ Γ E e τ φ,
    ctx𝔼 E →
    typing Γ .stat E⟦e⟧ τ φ →
    ∃ τ𝕖,
      sem_equiv_typing (erase_env Γ) (erase e) (erase e) (erase_ty τ𝕖) ∧
      sem_equiv_typing (erase_env ((τ𝕖, .stat) :: Γ)) (erase E⟦.fvar Γ.length⟧) (erase E⟦.fvar Γ.length⟧) (erase_ty τ) :=
  by
  intros Γ E e τ φ HE Hτ
  induction HE generalizing τ φ
  case hole =>
    exists τ
    constructor; apply fundamental; apply Hτ
    apply compatibility_fvar
    apply binds_erase_env; simp; rfl
  case cons𝔹 B E HB HE IH =>
    cases HB
    case appl₁ =>
      cases Hτ
      case app₁ Harg HX =>
        have ⟨τ𝕖, Hsem𝕖, HsemX⟩ := IH _ _ HX
        exists τ𝕖
        constructor; apply Hsem𝕖
        apply compatibility_app
        apply HsemX
        apply fundamental _ _ _ _ _ (weakening1 _ _ _ _ _ _ Harg)
    case appr₁ =>
      cases Hτ
      case app₁ HX Hf =>
        have ⟨τ𝕖, Hsem𝕖, HsemX⟩ := IH _ _ HX
        exists τ𝕖
        constructor; apply Hsem𝕖
        apply compatibility_app
        apply fundamental _ _ _ _ _ (weakening1 _ _ _ _ _ _ Hf)
        apply HsemX
    case appl₂ =>
      cases Hτ
      case app₂ HX Harg =>
        have ⟨τ𝕖, Hsem𝕖, HsemX⟩ := IH _ _ HX
        exists τ𝕖
        constructor; apply Hsem𝕖
        apply compatibility_app
        apply HsemX
        apply fundamental _ _ _ _ _ (weakening1 _ _ _ _ _ _ Harg)
    case appr₂ =>
      cases Hτ
      case app₂ Hf HX =>
        have ⟨τ𝕖, Hsem𝕖, HsemX⟩ := IH _ _ HX
        exists τ𝕖
        constructor; apply Hsem𝕖
        apply compatibility_app
        apply fundamental _ _ _ _ _ (weakening1 _ _ _ _ _ _ Hf)
        apply HsemX
    case lift =>
      cases Hτ
      case lift_lam τ𝕒 τ𝕓 _ _ HX =>
        apply IH (.arrow (.fragment τ𝕒) (.fragment τ𝕓) _); apply HX
      case lift_lit HX =>
        apply IH .nat; apply HX
    case lets e _ =>
      cases Hτ
      case lets HX Hclose He =>
        have ⟨τ𝕖, Hsem𝕖, HsemX⟩ := IH _ _ HX
        exists τ𝕖
        constructor; apply Hsem𝕖
        apply compatibility_lets
        . constructor
          . rw [← length_erase_env, ← erase_closed_at]
            apply closed_at𝔼; apply HE
            apply closed_inc; apply typing_closed; apply HX; simp; simp
          . rw [← length_erase_env, ← erase_closed_at]
            apply closed_inc; apply Hclose; simp
        . constructor
          . rw [← length_erase_env, ← erase_closed_at]
            apply closed_at𝔼; apply HE
            apply closed_inc; apply typing_closed; apply HX; simp; simp
          . rw [← length_erase_env, ← erase_closed_at]
            apply closed_inc; apply Hclose; simp
        . apply HsemX
        . rw [← erase_env, ← erase_open₀_comm]
          apply fundamental
          rw [← List.singleton_append, List.append_cons, ← length_erase_env]
          have HEq : open₀ ((τ𝕖, Stage.stat) :: Γ).length e = shiftl_at Γ.length [(τ𝕖, Stage.stat)].length (open₀ Γ.length e) :=
            by
            rw [shiftl_open₀_comm, shiftl_id]; rfl
            apply Hclose; rfl
          rw [HEq]; apply weakening_strengthened; apply He; rfl

theorem sem_reflect :
  ∀ Γ E b τ φ,
    ctx𝔼 E →
    typing Γ .stat (E (.reflect b)) τ φ →
    sem_equiv_typing (erase_env Γ) (erase E⟦.reflect b⟧) (.lets (erase b) (erase E⟦.code (.bvar 0)⟧)) (erase_ty τ) :=
  by
  intros Γ E b τ φ HE Hτ
  have ⟨τ𝕖, φ₀, φ₁, HEqφ, Hτr, HτE⟩ := decompose𝔼 _ _ _ _ _ HE Hτ
  constructor; constructor
  . rw [lc, ← erase_lc_at]; apply typing_regular; apply Hτ
  . rw [← length_erase_env, ← erase_closed_at]; apply typing_closed; apply Hτ
  constructor; constructor
  . constructor
    . rw [← erase_lc_at]; apply typing_regular _ _ _ _ _ Hτr
    . rw [← erase_lc_at]; apply lc_ctx𝔼; apply HE; simp
  . constructor
    . simp [← length_erase_env, ← erase_closed_at]; apply typing_closed _ _ _ _ _ Hτr
    . simp [← length_erase_env, ← erase_closed_at]; apply closed_at𝔼; apply HE
      apply typing_closed _ _ _ _ _ Hτ; simp
  intros γ₀ γ₁ HsemΓ
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := sem_equiv_env_impl_multi_wf _ _ _ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := sem_equiv_env_impl_length_eq _ _ _ HsemΓ
  have ⟨τ𝕖, Hsem𝕖, Hsem𝔼⟩ := sem_decompose𝔼 _ _ _ _ _ HE Hτ
  rw [sem_equiv_typing] at Hsem𝕖 Hsem𝔼
  have Hsem𝕖 := Hsem𝕖.right.right γ₀ γ₁ HsemΓ
  rw [sem_equiv_expr] at Hsem𝕖
  have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value⟩ := Hsem𝕖
  have ⟨Hvalue₀, Hvalue₁⟩ := sem_equiv_value_impl_value _ _ _ Hsem_value
  have ⟨Hwf₀, Hwf₁⟩ := sem_equiv_value_impl_wf _ _ _ Hsem_value
  have Hsem𝔼 := Hsem𝔼.right.right (v₀ :: γ₀) (v₁ :: γ₁) (sem_equiv_env.cons _ _ _ _ _ _ Hsem_value HsemΓ)
  apply sem_equiv_expr_stepn; apply Hsem𝔼
  . admit
  . simp
    -- left step
    apply pure_stepn_trans
    apply pure_stepn_at𝔹 _ _ _ (ctx𝔹.lets _ _) Hstepv₁
    apply multi_subst_lc_at; apply Hmulti_wf₁
    rw [← erase_lc_at]; apply lc_ctx𝔼; apply HE; simp
    -- head step
    apply pure_stepn.multi; apply pure_stepn.refl
    have HEq :
      open_subst v₁ (multi_subst γ₁ (erase E⟦.code (.bvar 0)⟧)) =
      multi_subst γ₁ (subst γ₁.length v₁ (erase E⟦.fvar Γ.length⟧)) :=
      by
        rw [← multi_subst_comm, open_subst, ← subst_intro γ₁.length]
        rw [← multi_subst_open₀_comm, ← open₀, ← erase_open₀_comm]
        rw [open_ctx𝔼_map, erase_ctx𝔼_map]
        rw [HEq₁, ← length_erase_env]; rfl
        apply HE; apply HE; rfl; apply Hmulti_wf₁
        apply closed_inc
        apply multi_subst_closed; apply Hmulti_wf₁
        rw [HEq₁, ← length_erase_env, ← erase_closed_at]
        apply closed_at𝔼; apply HE
        apply typing_closed; apply Hτ; simp
        omega; omega; apply Hwf₁.right; apply Hmulti_wf₁
    rw [← HEq]; apply pure_step.pure_step𝕄 id; apply ctx𝕄.hole
    constructor
    . apply value_lc; apply Hvalue₁
    . apply multi_subst_lc_at; apply Hmulti_wf₁
      rw [← erase_lc_at]
      apply lc_ctx𝔼; apply HE; simp
    apply head𝕄.lets; apply Hvalue₁

-- e₀ ↦ e₁ (under Γ)
-- Γ ⊢ e₀ : τ
-- ———————————————————————
-- |Γ| ⊨ |e₀| ≈ |e₁| : |τ|
theorem sem_preservation_strengthened :
  ∀ Γ e₀ e₁ τ φ,
    step_lvl Γ.length e₀ e₁ →
    typing Γ .stat e₀ τ φ →
    sem_equiv_typing (erase_env Γ) (erase e₀) (erase e₁) (erase_ty τ) :=
  by
  intros Γ e₀ e₁ τ φ
  generalize HEqlvl : Γ.length = lvl
  intros Hstep Hτ
  cases Hstep
  case step𝕄 HM Hlc Hhead𝕄 =>
    induction HM generalizing Γ τ φ
    case hole =>
      apply sem_preservation_head
      apply Hhead𝕄; apply Hτ
      apply preservation_head𝕄
      apply Hhead𝕄; apply Hlc; apply Hτ
    case cons𝔹 B M HB HM IH =>
      rw [← ctx_comp B M]
      apply sem_decompose𝔹; apply HB
      intros _ _; apply IH
      apply HEqlvl; apply Hτ
    case consℝ R M HR HM IH =>
      rw [← ctx_comp R M]
      apply sem_decomposeℝ; rw [HEqlvl]; apply HR
      apply lc_ctx𝕄; apply HM; apply Hlc
      intros _ _ _ HEqintro; apply IH
      simp; omega; apply Hτ
  case reflect HP HE Hlc =>
    cases HP
    case hole => apply sem_reflect; apply HE; apply Hτ
    case consℚ HQ =>
      induction HQ generalizing Γ τ φ
      case holeℝ HR =>
        apply sem_decomposeℝ; rw [HEqlvl]; apply HR
        apply lc_ctx𝔼; apply HE; apply Hlc
        intros _ _ _ _ Hτ
        apply sem_reflect; apply HE; apply Hτ; apply Hτ
      case cons𝔹 B Q HB HQ IH =>
        rw [← ctx_comp B Q]
        apply sem_decompose𝔹; apply HB
        intros _ _; apply IH
        apply HEqlvl; apply Hτ
      case consℝ R Q HR HQ IH =>
        rw [← ctx_comp R Q]
        apply sem_decomposeℝ; rw [HEqlvl]; apply HR
        apply lc_ctxℚ; apply HQ
        apply lc_ctx𝔼; apply HE; apply Hlc
        intros _ _ _ HEqintro; apply IH
        simp; omega; apply Hτ
