import CollapsingTowers.TwoLevelRec.CtxEquiv.Defs
import CollapsingTowers.TwoLevelRec.LogicalEquiv.Fundamental

-- Γ ⊢ e₀ ≤𝑐𝑖𝑢 e₁ : τ ≜
--   Γ ⊢ e₀ : τ ∧
--   Γ ⊢ e₁ : τ ∧
--   ∀ (⦰ ⊢ γ : Γ, ⦰ ⊢ E⟦⦰ ⊢ τ⟧ : τ𝕖).
--   E⟦γ(e₀)⟧⇓ → E⟦γ(e₁)⟧⇓
@[simp]
def ciu_approx (Γ : TEnv) (e₀ e₁: Expr) (τ : Ty) : Prop :=
  typing Γ 𝟚 e₀ τ ⊥ ∧
  typing Γ 𝟚 e₁ τ ⊥ ∧
    ∀ γ, typing.subst γ Γ →
    ∀ E τ𝕖,
      ctx𝔼 E →
      ObsCtxℂ ⦰ τ E ⦰ τ𝕖 →
      termination E⟦msubst γ e₀⟧ →
      termination E⟦msubst γ e₁⟧

-- Γ ⊧ e₀ ≤𝑐𝑡𝑥 e₁ : τ
-- ——————————————————
-- Γ ⊢ e₀ ≤𝑐𝑖𝑢 e₁ : τ
theorem ctx_approx_impl_ciu_approx :
  ∀ Γ τ e₀ e₁,
    ctx_approx Γ e₀ e₁ τ →
    ciu_approx Γ e₀ e₁ τ :=
  by
  intros Γ τ e₀ e₁ Hctx
  constructor; apply Hctx.left
  constructor; apply Hctx.right.left
  intros γ Hγ
  induction Hγ generalizing e₀ e₁
  case nil =>
    intros E τ𝕖 HE
    apply Hctx.right.right
  case cons v γ τ𝕧 Γ Hvalue Hτv Hτγ IH =>
    intros E τ𝕖 HE HCE Htermination₀
    have HEq := typing.subst.length _ _ Hτγ
    have HsemΓ := log_approx_env.refl 0 _ _ Hτγ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.mwf _ _ _ _ HsemΓ
    have ⟨Hτe₀, Hτe₁, _⟩ := Hctx
    have HEqSubst₀ : msubst γ (subst (List.length Γ) v e₀) = opening 0 (msubst γ v) (msubst γ {0 ↤ List.length Γ}e₀) :=
      by
      rw [← comm.msubst_opening_value, ← intro.subst, identity.opening_closing]
      apply typing.regular _ _ _ _ _ Hτe₀
      rw [← closed.under_closing]; apply typing.closed_at_env _ _ _ _ _ Hτe₀
      apply Hmwf₀
    have HEqSubst₁ : msubst γ (subst (List.length Γ) v e₁) = opening 0 (msubst γ v) (msubst γ {0 ↤ List.length Γ}e₁) :=
      by
      rw [← comm.msubst_opening_value, ← intro.subst, identity.opening_closing]
      apply typing.regular _ _ _ _ _ Hτe₁
      rw [← closed.under_closing]; apply typing.closed_at_env _ _ _ _ _ Hτe₁
      apply Hmwf₁
    --
    --
    -- (x ↦ τ𝕧, Γ) ⊧ e₀ ≤𝑐𝑡𝑥 e₁ : τ
    -- ————————————————————————————————
    -- Γ ⊧ λx.e₀ @ v ≤𝑐𝑡𝑥 λx.e₁ @ v : τ
    have Hctx : ctx_approx Γ (.app₁ (.lam {0 ↤ Γ.length}e₀) v) (.app₁ (.lam {0 ↤ Γ.length}e₁) v) τ :=
      by
      apply ctx_approx.congruence_under_ObsCtxℂ _ _ _ _ _ _ _ Hctx
      have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ Hτv
      have Hτv := typing.weakening _ Γ _ _ _ _ Hτv
      simp at Hτv
      have HC₀ := ObsCtxℂ.hole Γ τ
      have HB₀ := ObsCtx𝔹.appl₁ Γ v τ𝕧 τ Hτv
      have HC₁ := ObsCtxℂ.cons𝔹 _ _ _ _ _ _ _ _ HC₀ HB₀
      have HB₁ := ObsCtx𝔹.lam Γ τ𝕧 τ Hwbt
      apply ObsCtxℂ.cons𝔹 _ _ _ _ _ _ _ _ HC₁ HB₁
    have ⟨Hτ₀, Hτ₁, _⟩ := Hctx
    have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ Hτ₀ Hτ₁ HsemΓ
    have HSτE₀ := typing.congruence_under_ObsCtxℂ _ _ _ _ _ _ HSτ₀ HCE
    have HSτE₁ := typing.congruence_under_ObsCtxℂ _ _ _ _ _ _ HSτ₁ HCE
    have ⟨Hlc₀, Hclosed₀⟩ := typing.wf _ _ _ _ _ HSτ₀
    have ⟨Hlc₁, Hclosed₁⟩ := typing.wf _ _ _ _ _ HSτ₁
    simp at Hlc₀ Hlc₁ Hclosed₀ Hclosed₁
    --
    --
    -- E⟦(x ↦ v, γ)e₀⟧⇓
    -- ————————————————
    -- E⟦λx.e₀ @ v⟧⇓
    have Htermination₀ : termination (E (msubst γ (({0 ↤ List.length Γ}e₀).lam.app₁ v))) :=
      by
      have ⟨v₀, Hvalue₀, Hstep₀⟩ := Htermination₀
      exists v₀
      constructor
      . apply Hvalue₀
      . apply stepn.multi _ _ _ _ Hstep₀
        apply step_grounded.congruence_under_ctx𝔼 _ _ _ HE (typing.dynamic_impl_grounded _ _ _ _ HSτ₀)
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . simp [Hlc₀]
        . simp [HEq, HEqSubst₀]
          apply head.app₁; rw [identity.msubst]
          apply Hvalue; apply typing.closed_at_env _ _ _ _ _ Hτv
    --
    --
    -- E⟦λx.e₁ @ v⟧⇓
    -- ————————————————
    -- E⟦(x ↦ v, γ)e₁⟧⇓
    have ⟨v₁, Hvalue₁, Hstep₁⟩ := IH _ _ Hctx _ _ HE HCE Htermination₀
    exists v₁
    constructor
    . apply Hvalue₁
    . have ⟨j, Hstep₁⟩ := stepn_impl_stepn_indexed _ _ Hstep₁
      have ⟨_, _, v𝕖, _, Hvalue𝕖, Hstep𝕖₁, HstepE₁⟩ := stepn_indexed.refine_at_ctx𝔼 _ _ _ _ HE Hvalue₁ (typing.dynamic_impl_grounded _ _ _ _ HSτE₁) Hstep₁
      simp at Hstep𝕖₁
      have HvalueFun : value (msubst γ {0 ↤ List.length Γ}e₁).lam := value.lam _ Hlc₁.left
      have HvalueArg : value (msubst γ v) := by rw [identity.msubst _ _ (typing.closed_at_env _ _ _ _ _ Hτv)]; apply Hvalue
      have ⟨_, _, Hstep𝕖₁⟩ := stepn_indexed.refine.app₁.eliminator _ _ _ _ HvalueFun HvalueArg Hvalue𝕖 Hstep𝕖₁
      have Hstep𝕖₁ := stepn_indexed_impl_stepn _ _ _ Hstep𝕖₁
      have HstepE₁ := stepn_indexed_impl_stepn _ _ _ HstepE₁
      apply stepn.trans _ _ _ _ HstepE₁
      simp [HEq, HEqSubst₁]
      apply stepn_grounded.congruence_under_ctx𝔼 _ _ _ HE (
        by
        have HG₁ := typing.dynamic_impl_grounded _ _ _ _ HSτ₁
        simp at HG₁
        apply grounded.under_opening_value
        . apply HG₁.right
        . apply HG₁.left
      ) Hstep𝕖₁

-- Γ ⊧ e₀ ≤𝑐𝑖𝑢 e₁ : τ
-- ——————————————————
-- Γ ⊢ e₀ ≤𝑙𝑜𝑔 e₁ : τ
theorem ciu_approx_impl_log_approx :
  ∀ Γ τ e₀ e₁,
    ciu_approx Γ e₀ e₁ τ →
    log_approx Γ e₀ e₁ τ :=
  by
  intros Γ τ e₀ e₁ Hciu
  admit
