import CollapsingTowers.TwoLevelRec.LogicalEquiv.Defs
import CollapsingTowers.TwoLevelRec.Erasure.Defs

lemma consistency.erase_ctx𝔼 :
  ∀ E Γ e τ φ k γ₀ γ₁,
    ctx𝔼 E →
    typing Γ 𝟙 E⟦e⟧ τ φ →
    log_approx_env k γ₀ γ₁ ‖Γ‖𝛾 →
    (∃ E₀, ctx𝔼 E₀ ∧ (∀ e, multi_subst γ₀ ‖E⟦e⟧‖ = E₀⟦multi_subst γ₀ ‖e‖⟧)) ∧
    (∃ E₁, ctx𝔼 E₁ ∧ (∀ e, multi_subst γ₁ ‖E⟦e⟧‖ = E₁⟦multi_subst γ₁ ‖e‖⟧)) :=
  by
  intros E Γ e τ φ k γ₀ γ₁ HE Hτ HsemΓ
  induction HE generalizing τ φ
  case hole =>
    constructor
    . exists id; constructor; apply ctx𝔼.hole; simp
    . exists id; constructor; apply ctx𝔼.hole; simp
  case cons𝔹 HB HE IH =>
    have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := log_approx_env.multi_wf _ _ _ _ HsemΓ
    cases HB
    case appl₁ arg Hlc =>
      cases Hτ
      case app₁ Harg HX =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .app₁ X (multi_subst γ₀ ‖arg‖)) ∘ E₀
          constructor
          . apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appl₁ _ _) HE₀
            apply lc.under_multi_subst; apply Hmulti_wf₀
            rw [← lc.under_erase]; apply Hlc
          . simp; apply IH₀
        . exists (fun X => .app₁ X (multi_subst γ₁ ‖arg‖)) ∘ E₁
          constructor
          . apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appl₁ _ _) HE₁
            apply lc.under_multi_subst; apply Hmulti_wf₁
            rw [← lc.under_erase]; apply Hlc
          . simp; apply IH₁
    case appr₁ f HvalueFun =>
      cases Hτ
      case app₁ HX Hf =>
        cases HvalueFun with
        | lam e Hlc =>
          have ⟨IH₀, IH₁⟩ := IH _ _ HX
          have ⟨E₀, HE₀, IH₀⟩ := IH₀
          have ⟨E₁, HE₁, IH₁⟩ := IH₁
          constructor
          . exists (fun X => .app₁ (multi_subst γ₀ ‖.lam e‖) X) ∘ E₀
            constructor
            . apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appr₁ _ _) HE₀
              simp; apply value.lam
              apply lc.under_multi_subst; apply Hmulti_wf₀
              rw [← lc.under_erase]; apply Hlc
            . simp; apply IH₀
          . exists (fun X => .app₁ (multi_subst γ₁ ‖.lam e‖) X) ∘ E₁
            constructor
            . apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appr₁ _ _) HE₁
              simp; apply value.lam
              apply lc.under_multi_subst; apply Hmulti_wf₁
              rw [← lc.under_erase]; apply Hlc
            . simp; apply IH₁
        | _ => cases Hf
    case appl₂ arg Hlc =>
      cases Hτ
      case app₂ HX Harg =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .app₁ X (multi_subst γ₀ ‖arg‖)) ∘ E₀
          constructor
          . apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appl₁ _ _) HE₀
            apply lc.under_multi_subst; apply Hmulti_wf₀
            rw [← lc.under_erase]; apply Hlc
          . simp; apply IH₀
        . exists (fun X => .app₁ X (multi_subst γ₁ ‖arg‖)) ∘ E₁
          constructor
          . apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appl₁ _ _) HE₁
            apply lc.under_multi_subst; apply Hmulti_wf₁
            rw [← lc.under_erase]; apply Hlc
          . simp; apply IH₁
    case appr₂ f HvalueFun =>
      cases Hτ
      case app₂ Hf HX =>
        cases HvalueFun with
        | code e Hlc =>
          cases Hf with
          | code_fragment _ x _ HBinds =>
            have HBinds := env.erase.binds _ _ _ _ HBinds
            have Hsem_value := log_approx_env.binds_log_approx_value _ _ _ _ _ _ HsemΓ HBinds
            have ⟨Hvalue₀, Hvalue₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value
            have ⟨IH₀, IH₁⟩ := IH _ _ HX
            have ⟨E₀, HE₀, IH₀⟩ := IH₀
            have ⟨E₁, HE₁, IH₁⟩ := IH₁
            constructor
            . exists (fun X => .app₁ (multi_subst γ₀ (.fvar x)) X) ∘ E₀
              constructor
              . apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appr₁ _ _) HE₀
                apply Hvalue₀
              . simp; apply IH₀
            . exists (fun X => .app₁ (multi_subst γ₁ (.fvar x)) X) ∘ E₁
              constructor
              . apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appr₁ _ _) HE₁
                apply Hvalue₁
              . simp; apply IH₁
        | _ => cases Hf
    case lift =>
      cases Hτ
      case lift_lam HX => apply IH _ _ HX
      case lift_lit HX => apply IH _ _ HX
    case lets e Hlc =>
      cases Hτ
      case lets HX Hclose He =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .lets X (multi_subst γ₀ ‖e‖)) ∘ E₀
          constructor
          . apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.lets _ _) HE₀
            apply lc.under_multi_subst; apply Hmulti_wf₀
            rw [← lc.under_erase]; apply Hlc
          . simp; apply IH₀
        . exists (fun X => .lets X (multi_subst γ₁ ‖e‖)) ∘ E₁
          constructor
          . apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.lets _ _) HE₁
            apply lc.under_multi_subst; apply Hmulti_wf₁
            rw [← lc.under_erase]; apply Hlc
          . simp; apply IH₁
    case fix₁ =>
      cases Hτ
      case fix₁ HX =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .fix₁ X) ∘ E₀
          constructor
          . apply ctx𝔼.cons𝔹 _ _ ctx𝔹.fix₁ HE₀
          . simp; apply IH₀
        . exists (fun X => .fix₁ X) ∘ E₁
          constructor
          . apply ctx𝔼.cons𝔹 _ _ ctx𝔹.fix₁ HE₁
          . simp; apply IH₁
    case fix₂ =>
      cases Hτ
      case fix₂ HX =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .fix₁ X) ∘ E₀
          constructor
          . apply ctx𝔼.cons𝔹 _ _ ctx𝔹.fix₁ HE₀
          . simp; apply IH₀
        . exists (fun X => .fix₁ X) ∘ E₁
          constructor
          . apply ctx𝔼.cons𝔹 _ _ ctx𝔹.fix₁ HE₁
          . simp; apply IH₁

-- Γ ⊢ E⟦reflect b⟧ : τ
-- ——————————————————————————————————————————————————————————
-- ‖Γ‖ ⊨ ‖E⟦reflect b⟧‖ ≈𝑙𝑜𝑔 ‖lets𝕔 x = b in ‖E⟦code x⟧‖ : ‖τ‖
theorem consistency.reflect :
  ∀ Γ E b τ φ,
    ctx𝔼 E →
    typing Γ 𝟙 E⟦.reflect b⟧ τ φ →
    log_equiv ‖Γ‖𝛾 ‖E⟦.reflect b⟧‖ ‖.lets𝕔 b E⟦.code (.bvar 0)⟧‖ ‖τ‖𝜏 :=
  by
  intros Γ E b τ φ HE Hτ₀
  have ⟨τ𝕖, φ₀, φ₁, HEqφ, Hτr₀, HτE₀⟩ := preservation.under_ctx𝔼 _ _ _ _ _ HE Hτ₀
  cases Hτr₀
  case reflect τ𝕖 Hτb₀ =>
    have HτE₀ : typing ((.fragment τ𝕖, 𝟙) :: Γ) 𝟙 E⟦.fvar Γ.length⟧ τ φ₁ :=
      by
      rw [← List.singleton_append, ← union_pure_left φ₁]
      apply HτE₀
      apply typing.fvar
      . simp
      . simp; apply And.left
        apply typing.wbt_pure_at_dyn
        apply Hτb₀
    have HEτ₀ := typing.erase_safety _ _ _ _ _ Hτ₀
    have HEτb₀ := typing.erase_safety _ _ _ _ _ Hτb₀
    have HEτE₀ := typing.erase_safety _ _ _ _ _ HτE₀
    have HEτ₁ : typing ‖Γ‖𝛾 𝟚 ‖.lets𝕔 b E⟦.code (.bvar 0)⟧‖ ‖τ‖𝜏 ∅ :=
      by
      simp; rw [← erase.under_ctx𝔼 _ _ HE]; simp
      rw [← union_pure_left ∅]
      apply typing.lets
      . apply HEτb₀
      . rw [← env.erase.length, ← comm.erase_opening, opening.under_ctx𝔼 _ _ _ _ HE]
        apply HEτE₀
      . apply ty.erase.wbt
      . rw [← env.erase.length, ← closed.under_erase]
        apply closed.under_ctx𝔼 _ _ _ _ HE
        apply typing.closed_at_env; apply Hτ₀; simp
    constructor
    -- left approximation
    . constructor; apply HEτ₀
      constructor; apply HEτ₁
      intros k γ₀ γ₁ HsemΓ
      have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := log_approx_env.multi_wf _ _ _ _ HsemΓ
      have ⟨HEq₀, HEq₁⟩ := log_approx_env.length _ _ _ _ HsemΓ
      have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.multi_subst.typing _ _ _ _ _ _ _ HEτ₀ HEτ₁ HsemΓ
      have ⟨HSτb₀, HSτb₁⟩ := log_approx_env.multi_subst.typing _ _ _ _ _ _ _ HEτb₀ HEτb₀ HsemΓ
      --
      --
      -- (γ₀, γ₁) ∈ 𝓖⟦‖Γ‖⟧{k}
      -- ————————————————————
      -- γ₀‖E⟦X⟧‖ = E₀⟦γ₀‖X‖⟧
      -- γ₁‖E⟦X⟧‖ = E₁⟦γ₀‖X‖⟧
      have ⟨HE₀, HE₁⟩ := consistency.erase_ctx𝔼 _ _ _ _ _ _ _ _ HE Hτ₀ HsemΓ
      have ⟨E₀, HE₀, HEqE₀⟩ := HE₀
      have ⟨E₁, HE₁, HEqE₁⟩ := HE₁
      simp [HEqE₀, HEqE₁] at HSτ₀ HSτ₁
      have ⟨HlcE₀, HclosedE₀⟩ := typing.wf _ _ _ _ _ HSτ₀
      have ⟨HlcE₁, HclosedE₁⟩ := typing.wf _ _ _ _ _ HSτ₁
      --
      --
      -- E₀⟦γ₀‖b‖⟧ ⇝ ⟦j⟧ v₀
      -- ——————————————————
      -- i₀ + i₁ = j
      -- γ₀‖b‖ ⇝ ⟦i₀⟧ bv₀
      -- E₀⟦bv₀⟧ ⇝ ⟦i₁⟧ v₀
      simp [HEqE₀, HEqE₁]
      intros j Hindexj v₀ Hvalue₀ Hstep₀
      have ⟨i₀, i₁, bv₀, HEqj, HvalueBind₀, HstepBind₀, HstepE₀⟩ := stepn_indexed.refine_at_ctx𝔼 _ _ _ _ HE₀ Hvalue₀ (typing.grounded_at_dyn _ _ _ _ HSτ₀) Hstep₀
      --
      --
      -- γ₀‖b‖ ⇝ ⟦i₀⟧ bv₀
      -- ‖Γ‖ ⊧ ‖b‖ ≤𝑙𝑜𝑔 ‖b‖ : ‖τ𝕖‖
      -- —————————————————————————
      -- γ₁‖b‖ ⇝* bv₁
      -- (bv₀, bv₁) ∈ 𝓥⟦‖τ𝕖‖⟧{k - i₀}
      have ⟨_, _, IHb⟩ := log_approx.fundamental _ _ _ HEτb₀
      simp only [log_approx_expr] at IHb
      have ⟨bv₁, HstepBind₁, Hsem_value_bind⟩ := IHb _ _ _ HsemΓ i₀ (by omega) _ HvalueBind₀ HstepBind₀
      have ⟨HvalueBind₀, HvalueBind₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value_bind
      have ⟨HτBind₀, HτBind₁⟩ := log_approx_value.syntactic.typing _ _ _ _ Hsem_value_bind
      have ⟨HlcBind₀, HclosedBind₀⟩ := typing.wf _ _ _ _ _ HτBind₀
      have ⟨HlcBind₁, HclosedBind₁⟩ := typing.wf _ _ _ _ _ HτBind₁
      --
      --
      -- ‖Γ‖ ⊧ ‖E⟦x⟧‖ ≤𝑙𝑜𝑔 ‖E⟦x⟧‖ : ‖τ‖
      -- (bv₀, bv₁) ∈ 𝓥⟦‖τ𝕖‖⟧{k - i₀}
      -- ———————————————————————————————————————————————————————————
      -- ((x ↦ bv₀, γ₀)‖E⟦x⟧‖, (x ↦ bv₁, γ₁)‖E⟦x⟧‖) ∈ 𝓔⟦‖τ‖⟧{k - i₀}
      have ⟨_, _, IHE⟩ := log_approx.fundamental _ _ _ HEτE₀
      have Hsem_exprE := IHE (k - i₀) (bv₀ :: γ₀) (bv₁ :: γ₁) (
        by
        apply log_approx_env.cons; apply Hsem_value_bind
        apply log_approx_env.antimono; apply HsemΓ; omega
      )
      --
      --
      -- ((x ↦ bv₀, γ₀)‖E⟦x⟧‖, (x ↦ bv₁, γ₁)‖E⟦x⟧‖) ∈ 𝓔⟦‖τ‖⟧{k - i₀}
      -- ———————————————————————————————————————————————————————————
      -- (E₀⟦bv₀⟧, E₁⟦bv₁⟧) ∈ 𝓔⟦‖τ‖⟧{k - i₀}
      have HEqE₀ : (multi_subst (bv₀ :: γ₀) ‖E⟦.fvar Γ.length⟧‖) = E₀⟦bv₀⟧:=
        by
        rw [env.erase.length, ← HEq₀]
        rw [multi_subst, ← comm.multi_subst_subst _ _ _ _ (by omega) HclosedBind₀ Hmulti_wf₀]
        rw [HEqE₀, subst.under_ctx𝔼 _ _ _ _ _ HE₀]
        simp; apply closed.inc; apply HclosedE₀; simp
      have HEqE₁ : (multi_subst (bv₁ :: γ₁) ‖E⟦.fvar Γ.length⟧‖) = E₁⟦bv₁⟧:=
        by
        rw [env.erase.length, ← HEq₁]
        rw [multi_subst, ← comm.multi_subst_subst _ _ _ _ (by omega) HclosedBind₁ Hmulti_wf₁]
        rw [HEqE₁, subst.under_ctx𝔼 _ _ _ _ _ HE₁]
        simp; apply closed.inc; apply HclosedE₁.right; simp
      rw [HEqE₀, HEqE₁] at Hsem_exprE
      --
      --
      -- E₀⟦bv₀⟧ ⇝ ⟦i₁⟧ v₀
      -- (E₀⟦bv₀⟧, E₁⟦bv₁⟧) ∈ 𝓔⟦‖τ‖⟧{k - i₀}
      -- ———————————————————————————————————
      -- E₁⟦bv₁⟧ ⇝* v₁
      -- (v₀, v₁) ∈ 𝓥⟦‖τ‖⟧{k - i₀ - i₁}
      simp only [log_approx_expr] at Hsem_exprE
      have ⟨v₁, HstepE₁, Hsem_value⟩ := Hsem_exprE i₁ (by omega) _ Hvalue₀ HstepE₀
      --
      --
      -- γ₁‖b‖ ⇝* bv₁
      -- E₁⟦bv₁⟧ ⇝* v₁
      -- ——————————————————————————————
      -- lets x = γ₁‖b‖ in E₁⟦x⟧ ⇝* v₁
      exists v₁
      constructor
      . apply stepn.trans
        apply stepn.grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.lets _ HlcE₁.right) (typing.grounded_at_dyn _ _ _ _ HSτb₁) HstepBind₁
        apply stepn.multi _ _ _ _ HstepE₁
        apply step_lvl.pure id; apply ctx𝕄.hole
        . constructor
          . apply HlcBind₁
          . apply lc.under_ctx𝔼; apply HE₁; simp
        . have HEq : E₁⟦bv₁⟧ = opening 0 bv₁ E₁⟦.bvar 0⟧ :=
            by rw [opening.under_ctx𝔼 _ _ _ _ HE₁]; rfl
          rw [HEq]
          apply head.lets; apply HvalueBind₁
      . apply log_approx_value.antimono
        apply Hsem_value; omega
    -- right approximation
    . constructor; apply HEτ₁
      constructor; apply HEτ₀
      intros k γ₀ γ₁ HsemΓ
      have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := log_approx_env.multi_wf _ _ _ _ HsemΓ
      have ⟨HEq₀, HEq₁⟩ := log_approx_env.length _ _ _ _ HsemΓ
      have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.multi_subst.typing _ _ _ _ _ _ _ HEτ₁ HEτ₀ HsemΓ
      have ⟨HSτb₀, HSτb₁⟩ := log_approx_env.multi_subst.typing _ _ _ _ _ _ _ HEτb₀ HEτb₀ HsemΓ
      --
      --
      -- (γ₀, γ₁) ∈ 𝓖⟦‖Γ‖⟧{k}
      -- ————————————————————
      -- γ₀‖E⟦X⟧‖ = E₀⟦γ₀‖X‖⟧
      -- γ₁‖E⟦X⟧‖ = E₁⟦γ₀‖X‖⟧
      have ⟨HE₀, HE₁⟩ := consistency.erase_ctx𝔼 _ _ _ _ _ _ _ _ HE Hτ₀ HsemΓ
      have ⟨E₀, HE₀, HEqE₀⟩ := HE₀
      have ⟨E₁, HE₁, HEqE₁⟩ := HE₁
      simp [HEqE₀, HEqE₁] at HSτ₀ HSτ₁
      --
      --
      -- lets x = γ₀‖b‖ in γ₀‖E⟦x⟧‖ ⇝ ⟦j⟧ v₀
      -- —————————————————————————————————————
      -- i₀ + 1 + i₁ = j
      -- γ₀‖b‖ ⇝ ⟦i₀⟧ bv₀
      -- E₀⟦bv₀⟧ ⇝ ⟦i₁⟧ v₀
      simp [HEqE₀, HEqE₁]
      have ⟨HlcE₀, HclosedE₀⟩ := typing.wf _ _ _ _ _ HSτ₀
      have ⟨HlcE₁, HclosedE₁⟩ := typing.wf _ _ _ _ _ HSτ₁
      intros j Hindexj v₀ Hvalue₀ Hstep₀
      have ⟨i₀, i₁, bv₀, HEqj, HvalueBind₀, HstepBind₀, HstepE₀⟩ :=
        stepn_indexed.refine.lets _ _ _ _ Hvalue₀ (typing.grounded_at_dyn _ _ _ _ HSτ₀) Hstep₀
      simp [opening.under_ctx𝔼 _ _ _ _ HE₀] at HstepE₀
      --
      --
      -- γ₀‖b‖ ⇝ ⟦i₀⟧ bv₀
      -- ‖Γ‖ ⊧ ‖b‖ ≤𝑙𝑜𝑔 ‖b‖ : ‖τ𝕖‖
      -- ————————————————————————————
      -- γ₁‖b‖ ⇝* bv₁
      -- (bv₀, bv₁) ∈ 𝓥⟦‖τ𝕖‖⟧{k - i₀}
      have ⟨_, _, IHb⟩ := log_approx.fundamental _ _ _ HEτb₀
      simp only [log_approx_expr] at IHb
      have ⟨bv₁, HstepBind₁, Hsem_value_bind⟩ := IHb _ _ _ HsemΓ i₀ (by omega) _ HvalueBind₀ HstepBind₀
      have ⟨HvalueBind₀, HvalueBind₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value_bind
      have ⟨HτBind₀, HτBind₁⟩ := log_approx_value.syntactic.typing _ _ _ _ Hsem_value_bind
      have ⟨HlcBind₀, HclosedBind₀⟩ := typing.wf _ _ _ _ _ HτBind₀
      have ⟨HlcBind₁, HclosedBind₁⟩ := typing.wf _ _ _ _ _ HτBind₁
      --
      --
      -- ‖Γ‖ ⊧ ‖E⟦x⟧‖ ≤𝑙𝑜𝑔 ‖E⟦x⟧‖ : ‖τ‖
      -- (bv₀, bv₁) ∈ 𝓥⟦‖τ𝕖‖⟧{k - i₀}
      -- ———————————————————————————————————————————————————————————
      -- ((x ↦ bv₀, γ₀)‖E⟦x⟧‖, (x ↦ bv₁, γ₁)‖E⟦x⟧‖) ∈ 𝓔⟦‖τ‖⟧{k - i₀}
      have ⟨_, _, IHE⟩ := log_approx.fundamental _ _ _ HEτE₀
      have Hsem_exprE := IHE (k - i₀) (bv₀ :: γ₀) (bv₁ :: γ₁) (
        by
        apply log_approx_env.cons; apply Hsem_value_bind
        apply log_approx_env.antimono; apply HsemΓ; omega
      )
      --
      --
      -- ((x ↦ bv₀, γ₀)‖E⟦x⟧‖, (x ↦ bv₁, γ₁)‖E⟦x⟧‖) ∈ 𝓔⟦‖τ‖⟧{k - i₀}
      -- ———————————————————————————————————————————————————————————
      -- (E₀⟦bv₀⟧, E₁⟦bv₁⟧) ∈ 𝓔⟦‖τ‖⟧{k - i₀}
      have HEqE₀ : (multi_subst (bv₀ :: γ₀) ‖E⟦.fvar Γ.length⟧‖) = E₀⟦bv₀⟧:=
        by
        rw [env.erase.length, ← HEq₀]
        rw [multi_subst, ← comm.multi_subst_subst _ _ _ _ (by omega) HclosedBind₀ Hmulti_wf₀]
        rw [HEqE₀, subst.under_ctx𝔼 _ _ _ _ _ HE₀]
        simp; apply closed.inc; apply HclosedE₀.right; simp
      have HEqE₁ : (multi_subst (bv₁ :: γ₁) ‖E⟦.fvar Γ.length⟧‖) = E₁⟦bv₁⟧:=
        by
        rw [env.erase.length, ← HEq₁]
        rw [multi_subst, ← comm.multi_subst_subst _ _ _ _ (by omega) HclosedBind₁ Hmulti_wf₁]
        rw [HEqE₁, subst.under_ctx𝔼 _ _ _ _ _ HE₁]
        simp; apply closed.inc; apply HclosedE₁; simp
      rw [HEqE₀, HEqE₁] at Hsem_exprE
      --
      --
      -- E₀⟦bv₀⟧ ⇝ ⟦i₁⟧ v₀
      -- (E₀⟦bv₀⟧, E₁⟦bv₁⟧) ∈ 𝓔⟦‖τ‖⟧{k - i₀}
      -- ———————————————————————————————————
      -- E₁⟦bv₁⟧ ⇝* v₁
      -- (v₀, v₁) ∈ 𝓥⟦‖τ‖⟧{k - i₀ - i₁}
      simp only [log_approx_expr] at Hsem_exprE
      have ⟨v₁, HstepE₁, Hsem_value⟩ := Hsem_exprE i₁ (by omega) _ Hvalue₀ HstepE₀
      --
      --
      -- γ₁‖b‖ ⇝* bv₁
      -- E₁⟦bv₁⟧ ⇝* v₁
      -- ——————————————————————————————
      -- E₁⟦γ₁‖b‖⟧ ⇝* v₁
      -- (v₀, v₁) ∈ 𝓥⟦‖τ‖⟧{k - i₀ - i₁}
      exists v₁
      constructor
      . apply stepn.trans _ _ _ _ HstepE₁
        apply stepn.grounded.congruence_under_ctx𝔼 _ _ _ HE₁ (typing.grounded_at_dyn _ _ _ _ HSτb₁) HstepBind₁
      . apply log_approx_value.antimono
        apply Hsem_value; omega
