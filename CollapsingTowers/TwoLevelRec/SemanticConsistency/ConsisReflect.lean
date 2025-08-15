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
      --
      --
      -- (γ₀, γ₁) ∈ 𝓖⟦‖Γ‖⟧{k}
      -- ————————————————————
      -- γ₀‖E⟦X⟧‖ = E₀⟦γ₀‖X‖⟧
      -- γ₁‖E⟦X⟧‖ = E₁⟦γ₀‖X‖⟧
      have ⟨HE₀, HE₁⟩ := consistency.erase_ctx𝔼 _ _ _ _ _ _ _ _ HE Hτ₀ HsemΓ
      have ⟨E₀, HE₀, HEqE₀⟩ := HE₀
      have ⟨E₁, HE₁, HEqE₁⟩ := HE₁
      simp [HEqE₀, HEqE₁]
      --
      --
      -- ———————————————————————————————
      intros j Hindexj v₀ Hvalue₀ Hstep₀
      admit
    -- right approximation
    . constructor; apply HEτ₁
      constructor; apply HEτ₀
      admit
