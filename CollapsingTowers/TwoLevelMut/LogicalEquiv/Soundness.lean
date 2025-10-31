import CollapsingTowers.TwoLevelMut.LogicalEquiv.Fundamental
import CollapsingTowers.TwoLevelMut.CtxEquiv.Defs

lemma log_equiv.congruence_under_ObsCtx𝔹 :
  ∀ Δ Γ τδ τγ B e₀ e₁,
    log_equiv Δ e₀ e₁ τδ →
    ObsCtx𝔹 Δ τδ B Γ τγ →
    log_equiv Γ B⟦e₀⟧ B⟦e₁⟧ τγ :=
  by
  intros Δ Γ τδ τγ B e₀ e₁ HX HB
  have ⟨Hτ₀, Hτ₁, Hsem_expr⟩ := HX
  cases HB
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
    . apply log_equiv.fundamental _ _ _ Harg
  case appr₁ Hf =>
    apply compatibility.app₁
    . apply log_equiv.fundamental _ _ _ Hf
    . apply HX
  case letsl Hclosed He =>
    apply compatibility.lets
    . have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ Hτ₀
      apply Hwbt
    . apply Hclosed
    . apply Hclosed
    . apply HX
    . apply log_equiv.fundamental _ _ _ He
  case letsr Hb =>
    apply compatibility.lets
    . have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ Hb
      apply Hwbt
    . rw [← closed.under_closing]; apply typing.closed_at_env _ _ _ _ _ Hτ₀
    . rw [← closed.under_closing]; apply typing.closed_at_env _ _ _ _ _ Hτ₁
    . apply log_equiv.fundamental _ _ _ Hb
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
    . apply log_equiv.fundamental _ _ _ Hr
  case storer₁ Hl =>
    apply compatibility.store₁
    . apply log_equiv.fundamental _ _ _ Hl
    . apply HX

-- Δ ⊧ e₀ ≈𝑙𝑜𝑔 e₁ : τδ
-- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ
-- ————————————————————————
-- Γ ⊧ C⟦e₀⟧ ≈𝑙𝑜𝑔 C⟦e₁⟧ : τγ
lemma log_equiv.congruence_under_ObsCtxℂ :
  ∀ Δ Γ τδ τγ C e₀ e₁,
    log_equiv Δ e₀ e₁ τδ →
    ObsCtxℂ Δ τδ C Γ τγ →
    log_equiv Γ C⟦e₀⟧ C⟦e₁⟧ τγ :=
  by
  intros Δ Γ τδ τγ C e₀ e₁ Hsem HC
  induction HC generalizing e₀ e₁
  case hole => apply Hsem
  case cons𝔹 HB IH =>
    apply IH
    apply log_equiv.congruence_under_ObsCtx𝔹
    apply Hsem; apply HB

-- Γ ⊧ e₀ ≈𝑙𝑜𝑔 e₁ : τ
-- ——————————————————
-- Γ ⊧ e₀ ≈𝑐𝑡𝑥 e₁ : τ
theorem log_equiv.soundness :
  ∀ Γ τ e₀ e₁,
    log_equiv Γ e₀ e₁ τ →
    ctx_equiv Γ e₀ e₁ τ :=
  by
  intros Γ τ e₀ e₁ Hsem
  constructor; apply Hsem.left
  constructor; apply Hsem.right.left
  generalize HEqΔ : [] = Δ
  generalize HEqτδ : Ty.nat = τδ
  intros C HC
  induction HC generalizing e₀ e₁
  case hole =>
    rw [← HEqΔ, ← HEqτδ] at Hsem
    have ⟨Hτ₀, Hτ₁, Hsem_expr⟩ := Hsem
    simp only [log_equiv_expr] at Hsem_expr
    have ⟨𝓦, σ₀, σ₁, v₀, v₁, Hfuture, Hstep₀, Hstep₁, Hsem_store, Hsem_value⟩ := Hsem_expr World.empty _ _ (log_equiv_env.nil _) ϵ ϵ (by simp)
    cases v₀ <;> try simp at Hsem_value
    case lit n₀ =>
    cases v₁ <;> try simp at Hsem_value
    case lit n₁ =>
    exists σ₀, σ₁, .lit n₀
    constructor; apply value.lit
    constructor; apply Hstep₀; simp [Hsem_value]; apply Hstep₁
  case cons𝔹 C B HC HB IH =>
    apply IH
    apply log_equiv.congruence_under_ObsCtx𝔹
    apply Hsem; apply HB; apply HEqΔ; apply HEqτδ
