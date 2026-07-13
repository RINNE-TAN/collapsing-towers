import Instar.TwoLevelFinal.LogicalEquiv.Fundamental
import Instar.TwoLevelFinal.CtxEquiv.Defs

lemma log_approx.congruence_under_ObsCtx𝔽 :
  ∀ Δ Γ τδ τγ F e₀ e₁,
    log_approx Δ e₀ e₁ τδ →
    ObsCtx𝔽 Δ τδ F Γ τγ →
    log_approx Γ F⟦e₀⟧ F⟦e₁⟧ τγ :=
  by
  intros Δ Γ τδ τγ F e₀ e₁ HX HF
  have ⟨Hτ₀, Hτ₁, Hsem_expr⟩ := HX
  cases HF
  case lam Hwbt =>
    apply compatibility.lam
    . apply Hwbt
    . rw [← closed.under_closing]; apply typing.closed_at_env _ _ _ _ _ Hτ₀
    . rw [← closed.under_closing]; apply typing.closed_at_env _ _ _ _ _ Hτ₁
    . rw [identity.opening_closing, identity.opening_closing]
      apply HX
      apply typing.regular; apply Hτ₁
      apply typing.regular; apply Hτ₀
  case appl₁ Harg =>
    apply compatibility.app₁
    . apply HX
    . apply log_approx.fundamental _ _ _ Harg
  case appr₁ Hf =>
    apply compatibility.app₁
    . apply log_approx.fundamental _ _ _ Hf
    . apply HX
  case binaryl₁ Hr =>
    apply compatibility.binary₁
    . apply HX
    . apply log_approx.fundamental _ _ _ Hr
  case binaryr₁ Hl =>
    apply compatibility.binary₁
    . apply log_approx.fundamental _ _ _ Hl
    . apply HX
  case letsl Hclosed He =>
    apply compatibility.lets
    . have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ Hτ₀
      apply Hwbt
    . apply Hclosed
    . apply Hclosed
    . apply HX
    . apply log_approx.fundamental _ _ _ He
  case letsr τ𝕒 τ𝕓 Hb =>
    apply compatibility.lets
    . have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ Hb
      apply Hwbt
    . rw [← closed.under_closing]; apply typing.closed_at_env _ _ _ _ _ Hτ₀
    . rw [← closed.under_closing]; apply typing.closed_at_env _ _ _ _ _ Hτ₁
    . apply log_approx.fundamental _ _ _ Hb
    . rw [identity.opening_closing, identity.opening_closing]
      apply HX
      apply typing.regular; apply Hτ₁
      apply typing.regular; apply Hτ₀
  case alloc₁ =>
    apply compatibility.alloc₁
    apply HX
  case load₁ =>
    apply compatibility.load₁
    apply HX
  case storel₁ Hr =>
    apply compatibility.store₁
    . apply HX
    . apply log_approx.fundamental _ _ _ Hr
  case storer₁ Hl =>
    apply compatibility.store₁
    . apply log_approx.fundamental _ _ _ Hl
    . apply HX
  case fix₁ =>
    apply compatibility.fix₁
    apply HX
  case ifz₁ Hl Hr =>
    apply compatibility.ifz₁
    . apply HX
    . apply log_approx.fundamental _ _ _ Hl
    . apply log_approx.fundamental _ _ _ Hr
  case ifzl₁ Hc Hr =>
    apply compatibility.ifz₁
    . apply log_approx.fundamental _ _ _ Hc
    . apply HX
    . apply log_approx.fundamental _ _ _ Hr
  case ifzr₁ Hc Hl =>
    apply compatibility.ifz₁
    . apply log_approx.fundamental _ _ _ Hc
    . apply log_approx.fundamental _ _ _ Hl
    . apply HX

-- Δ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τδ
-- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ
-- ————————————————————————
-- Γ ⊧ C⟦e₀⟧ ≤𝑙𝑜𝑔 C⟦e₁⟧ : τγ
lemma log_approx.congruence_under_ObsCtxℂ :
  ∀ Δ Γ τδ τγ C e₀ e₁,
    log_approx Δ e₀ e₁ τδ →
    ObsCtxℂ Δ τδ C Γ τγ →
    log_approx Γ C⟦e₀⟧ C⟦e₁⟧ τγ :=
  by
  intros Δ Γ τδ τγ C e₀ e₁ Hsem HC
  induction HC generalizing e₀ e₁
  case hole => apply Hsem
  case cons𝔽 HF IH =>
    apply IH
    apply log_approx.congruence_under_ObsCtx𝔽
    apply Hsem; apply HF

-- Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ
-- ——————————————————
-- Γ ⊧ e₀ ≤𝑐𝑡𝑥 e₁ : τ
theorem log_approx.soundness :
  ∀ Γ τ e₀ e₁,
    log_approx Γ e₀ e₁ τ →
    ctx_approx Γ e₀ e₁ τ :=
  by
  intros Γ τ e₀ e₁ Hsem
  constructor; apply Hsem.left
  constructor; apply Hsem.right.left
  generalize HEqΔ : ⦰ = Δ
  intros C τ𝕔 HC Htermination
  induction HC generalizing e₀ e₁
  case hole =>
    have ⟨v₀, σ₀, Hvalue₀, Hstep₀⟩ := Htermination
    have ⟨k, Hstep₀⟩ := stepn_impl_stepn_indexed _ _ Hstep₀
    rw [← HEqΔ] at Hsem
    have ⟨_, _, Hsem_expr⟩ := Hsem
    simp only [log_approx_expr] at Hsem_expr
    have ⟨_, σ₁, v₁, _, Hstep₁, _, Hsem_value⟩ :=
      Hsem_expr (k + 1) World.empty _ _ (log_approx_env.nil _ _) k (by omega) ϵ ϵ (by simp) _ _ Hvalue₀ Hstep₀
    have ⟨_, Hvalue₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value
    exists v₁, σ₁
  case cons𝔽 C F HC HF IH =>
    apply IH
    apply log_approx.congruence_under_ObsCtx𝔽
    apply Hsem; apply HF; apply HEqΔ; apply Htermination

-- Γ ⊧ e₀ ≈𝑙𝑜𝑔 e₁ : τ
-- ——————————————————
-- Γ ⊧ e₀ ≈𝑐𝑡𝑥 e₁ : τ
theorem log_equiv.soundness :
  ∀ Γ τ e₀ e₁,
    log_equiv Γ e₀ e₁ τ →
    ctx_equiv Γ e₀ e₁ τ :=
  by
  intros Γ τ e₀ e₁ Hsem
  constructor
  . apply log_approx.soundness _ _ _ _ Hsem.left
  . apply log_approx.soundness _ _ _ _ Hsem.right
