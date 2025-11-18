import CollapsingTowers.TwoLevelBasic.OperationalSemantics.Defs
import CollapsingTowers.TwoLevelBasic.SyntacticTyping.Defs

inductive ObsCtx𝔽 : TEnv → Ty → Ctx → TEnv → Ty → Prop where
  | lam :
    ∀ Γ τ𝕒 τ𝕓,
      wbt 𝟚 τ𝕒 →
      ObsCtx𝔽
        ((τ𝕒, 𝟚) :: Γ) τ𝕓
        (fun X => .lam ({0 ↤ Γ.length} X))
        Γ (.arrow τ𝕒 τ𝕓 ⊥)
  | appl₁ :
    ∀ Γ arg τ𝕒 τ𝕓,
      typing Γ 𝟚 arg τ𝕒 ⊥ →
      ObsCtx𝔽
        Γ (.arrow τ𝕒 τ𝕓 ⊥)
        (fun X => .app₁ X arg)
        Γ τ𝕓
  | appr₁ :
    ∀ Γ f τ𝕒 τ𝕓,
      typing Γ 𝟚 f (.arrow τ𝕒 τ𝕓 ⊥) ⊥ →
      ObsCtx𝔽
        Γ τ𝕒
        (fun X => .app₁ f X)
        Γ τ𝕓
  | letsl :
    ∀ Γ e τ𝕒 τ𝕓,
      closed_at e Γ.length →
      typing ((τ𝕒, 𝟚) :: Γ) 𝟚 ({0 ↦ Γ.length} e) τ𝕓 ⊥ →
      ObsCtx𝔽
        Γ τ𝕒
        (fun X => .lets X e)
        Γ τ𝕓
  | letsr :
    ∀ Γ b τ𝕒 τ𝕓,
      typing Γ 𝟚 b τ𝕒 ⊥ →
      ObsCtx𝔽
        ((τ𝕒, 𝟚) :: Γ) τ𝕓
        (fun X => .lets b ({0 ↤ Γ.length} X))
        Γ τ𝕓

-- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ ≜ ∀ (Δ ⊢ X : τδ). Γ ⊢ C⟦X⟧ : τγ
inductive ObsCtxℂ : TEnv → Ty → Ctx → TEnv → Ty → Prop where
  | hole : ∀ Γ Δ τ, ObsCtxℂ Γ τ id (Δ ++ Γ) τ
  | cons𝔽 :
    ∀ Ψ Δ Γ τψ τδ τγ C F,
      ObsCtxℂ Δ τδ C Γ τγ →
      ObsCtx𝔽 Ψ τψ F Δ τδ →
      ObsCtxℂ Ψ τψ (C ∘ F) Γ τγ

lemma ObsCtxℂ.consℂ :
  ∀ Ψ Δ Γ τψ τδ τγ C₀ C₁,
    ObsCtxℂ Δ τδ C₀ Γ τγ →
    ObsCtxℂ Ψ τψ C₁ Δ τδ →
    ObsCtxℂ Ψ τψ (C₀ ∘ C₁) Γ τγ :=
  by
  intros Ψ Δ Γ τψ τδ τγ C₀ C₁ HC₀ HC₁
  induction HC₁ generalizing C₀
  case hole => admit
  case cons𝔽 => admit

lemma typing.congruence_under_ObsCtx𝔽 :
  ∀ Δ Γ τδ τγ F X,
    typing Δ 𝟚 X τδ ⊥ →
    ObsCtx𝔽 Δ τδ F Γ τγ →
    typing Γ 𝟚 F⟦X⟧ τγ ⊥ :=
  by
  intros Δ Γ τδ τγ F X HX HF
  induction HF generalizing X
  case lam Hwbt =>
    apply typing.lam
    . rw [identity.opening_closing]
      apply HX; apply typing.regular; apply HX
    . apply Hwbt
    . rw [← closed.under_closing]
      apply typing.closed_at_env _ _ _ _ _ HX
  case appl₁ Harg =>
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.app₁; apply HX; apply Harg
  case appr₁ Hf =>
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.app₁; apply Hf; apply HX
  case letsl Hclosed He =>
    rw [← Effect.union_pure ⊥]
    apply typing.lets
    . apply HX
    . apply He
    . have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ HX
      apply Hwbt
    . apply Hclosed
  case letsr Hb =>
    rw [← Effect.union_pure ⊥]
    apply typing.lets
    . apply Hb
    . rw [identity.opening_closing]; apply HX
      apply typing.regular; apply HX
    . have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ Hb
      apply Hwbt
    . rw [← closed.under_closing]
      apply typing.closed_at_env _ _ _ _ _ HX

-- Δ ⊢ X : τδ
-- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ
-- ——————————————————
-- Γ ⊢ C⟦X⟧ : τγ
lemma typing.congruence_under_ObsCtxℂ :
  ∀ Δ Γ τδ τγ C X,
    typing Δ 𝟚 X τδ ⊥ →
    ObsCtxℂ Δ τδ C Γ τγ →
    typing Γ 𝟚 C⟦X⟧ τγ ⊥ :=
  by
  intros Δ Γ τδ τγ C X HX HC
  induction HC generalizing X
  case hole => apply typing.weakening _ _ _ _ _ _ HX
  case cons𝔽 HB IH =>
    apply IH; apply typing.congruence_under_ObsCtx𝔽
    apply HX; apply HB

-- Γ ⊧ e₀ ≈𝑐𝑡𝑥 e₁ : τ ≜
--   Γ ⊢ e₀ : τ ∧
--   Γ ⊢ e₁ : τ ∧
--   ∀ (⦰ ⊢ C⟦Γ ⊢ τ⟧ : ℕ).
--   ∀ v. C⟦e₀⟧ ⇝* v ↔ C⟦e₁⟧ ⇝* v
@[simp]
def ctx_equiv (Γ : TEnv) (e₀ e₁: Expr) (τ : Ty) : Prop :=
  typing Γ 𝟚 e₀ τ ⊥ ∧
  typing Γ 𝟚 e₁ τ ⊥ ∧
    ∀ C, ObsCtxℂ Γ τ C ⦰ .nat →
    ∀ v, value v → (
      (C⟦e₀⟧ ⇝* v) ↔ (C⟦e₁⟧ ⇝* v)
    )

lemma ctx_equiv.congruence_under_ObsCtx𝔽 :
  ∀ Δ Γ τδ τγ F e₀ e₁,
    ctx_equiv Δ e₀ e₁ τδ →
    ObsCtx𝔽 Δ τδ F Γ τγ →
    ctx_equiv Γ F⟦e₀⟧ F⟦e₁⟧ τγ :=
  by
  intros Δ Γ τδ τγ F e₀ e₁ Hctx HF
  have ⟨Hτ₀, Hτ₁, Hctx⟩ := Hctx
  constructor; apply typing.congruence_under_ObsCtx𝔽 _ _ _ _ _ _ Hτ₀ HF
  constructor; apply typing.congruence_under_ObsCtx𝔽 _ _ _ _ _ _ Hτ₁ HF
  intros C HC
  rw [ctx_comp C F, ctx_comp C F]
  apply Hctx
  apply ObsCtxℂ.cons𝔽; apply HC; apply HF

-- Δ ⊧ e₀ ≈𝑐𝑡𝑥 e₁ : τδ
-- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ
-- ————————————————————————
-- Γ ⊧ C⟦e₀⟧ ≈𝑐𝑡𝑥 C⟦e₁⟧ : τγ
lemma ctx_equiv.congruence_under_ObsCtxℂ :
  ∀ Δ Γ τδ τγ C e₀ e₁,
    ctx_equiv Δ e₀ e₁ τδ →
    ObsCtxℂ Δ τδ C Γ τγ →
    ctx_equiv Γ C⟦e₀⟧ C⟦e₁⟧ τγ :=
  by
  intros Δ Γ τδ τγ C e₀ e₁ Hctx HC
  induction HC generalizing e₀ e₁
  case hole =>
    have ⟨Hτ₀, Hτ₁, Hctx⟩ := Hctx
    constructor; apply typing.weakening _ _ _ _ _ _ Hτ₀
    constructor; apply typing.weakening _ _ _ _ _ _ Hτ₁
    intros C HC
    apply Hctx
    apply ObsCtxℂ.consℂ _ _ _ _ _ _ _ _ HC (ObsCtxℂ.hole _ _ _)
  case cons𝔽 HF IH =>
    apply IH
    apply ctx_equiv.congruence_under_ObsCtx𝔽
    apply Hctx; apply HF
