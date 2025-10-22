import CollapsingTowers.TwoLevelRec.OperationalSemantics.Defs
import CollapsingTowers.TwoLevelRec.SyntacticTyping.Defs

inductive ObsCtx𝔹 : TEnv → Ty → Ctx → TEnv → Ty → Prop where
  | lam :
    ∀ Γ τ𝕒 τ𝕓,
      wbt 𝟚 τ𝕒 →
      ObsCtx𝔹
        ((τ𝕒, 𝟚) :: Γ) τ𝕓
        (fun X => .lam ({0 ↤ Γ.length} X))
        Γ (.arrow τ𝕒 τ𝕓 ⊥)
  | appl₁ :
    ∀ Γ arg τ𝕒 τ𝕓,
      typing Γ 𝟚 arg τ𝕒 ⊥ →
      ObsCtx𝔹
        Γ (.arrow τ𝕒 τ𝕓 ⊥)
        (fun X => .app₁ X arg)
        Γ τ𝕓
  | appr₁ :
    ∀ Γ f τ𝕒 τ𝕓,
      typing Γ 𝟚 f (.arrow τ𝕒 τ𝕓 ⊥) ⊥ →
      ObsCtx𝔹
        Γ τ𝕒
        (fun X => .app₁ f X)
        Γ τ𝕓
  | binaryl₁ :
    ∀ Γ op r,
      typing Γ 𝟚 r .nat ⊥ →
      ObsCtx𝔹
        Γ .nat
        (fun X => .binary₁ op X r)
        Γ .nat
  | binaryr₁ :
    ∀ Γ op l,
      typing Γ 𝟚 l .nat ⊥ →
      ObsCtx𝔹
        Γ .nat
        (fun X => .binary₁ op l X)
        Γ .nat
  | letsl :
    ∀ Γ e τ𝕒 τ𝕓,
      closed_at e Γ.length →
      typing ((τ𝕒, 𝟚) :: Γ) 𝟚 ({0 ↦ Γ.length} e) τ𝕓 ⊥ →
      ObsCtx𝔹
        Γ τ𝕒
        (fun X => .lets X e)
        Γ τ𝕓
  | letsr :
    ∀ Γ b τ𝕒 τ𝕓,
      typing Γ 𝟚 b τ𝕒 ⊥ →
      ObsCtx𝔹
        ((τ𝕒, 𝟚) :: Γ) τ𝕓
        (fun X => .lets b ({0 ↤ Γ.length} X))
        Γ τ𝕓
  | fix₁ :
    ∀ Γ τ𝕒 τ𝕓,
      ObsCtx𝔹
        Γ (.arrow (.arrow τ𝕒 τ𝕓 ⊥) (.arrow τ𝕒 τ𝕓 ⊥) ⊥)
        (fun X => .fix₁ X)
        Γ (.arrow τ𝕒 τ𝕓 ⊥)
  | ifz₁ :
    ∀ Γ l r τ,
      typing Γ 𝟚 l τ ⊥ →
      typing Γ 𝟚 r τ ⊥ →
      ObsCtx𝔹
        Γ .nat
        (fun X => .ifz₁ X l r)
        Γ τ
  | ifzl₁ :
    ∀ Γ c r τ,
      typing Γ 𝟚 c .nat ⊥ →
      typing Γ 𝟚 r τ ⊥ →
      ObsCtx𝔹
        Γ τ
        (fun X => .ifz₁ c X r)
        Γ τ
  | ifzr₁ :
    ∀ Γ c l τ,
      typing Γ 𝟚 c .nat ⊥ →
      typing Γ 𝟚 l τ ⊥ →
      ObsCtx𝔹
        Γ τ
        (fun X => .ifz₁ c l X)
        Γ τ

-- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ ≜ ∀ (Δ ⊢ X : τδ). Γ ⊢ C⟦X⟧ : τγ
inductive ObsCtxℂ : TEnv → Ty → Ctx → TEnv → Ty → Prop where
  | hole : ∀ Γ τ, ObsCtxℂ Γ τ id Γ τ
  | cons𝔹 :
    ∀ Ψ Δ Γ τψ τδ τγ C B,
      ObsCtxℂ Δ τδ C Γ τγ →
      ObsCtx𝔹 Ψ τψ B Δ τδ →
      ObsCtxℂ Ψ τψ (C ∘ B) Γ τγ

lemma typing.congruence_under_ObsCtx𝔹 :
  ∀ Δ Γ τδ τγ B X,
    typing Δ 𝟚 X τδ ⊥ →
    ObsCtx𝔹 Δ τδ B Γ τγ →
    typing Γ 𝟚 B⟦X⟧ τγ ⊥ :=
  by
  intros Δ Γ τδ τγ B X HX HB
  cases HB
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
  case binaryl₁ Hr =>
    rw [← Effect.union_pure ⊥]
    apply typing.binary₁; apply HX; apply Hr
  case binaryr₁ Hl =>
    rw [← Effect.union_pure ⊥]
    apply typing.binary₁; apply Hl; apply HX
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
  case fix₁ =>
    apply typing.fix₁; simp; rfl; apply HX
  case ifz₁ Hl Hr =>
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.ifz₁; apply HX; apply Hl; apply Hr
  case ifzl₁ Hc Hr =>
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.ifz₁; apply Hc; apply HX; apply Hr
  case ifzr₁ Hc Hl =>
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.ifz₁; apply Hc; apply Hl; apply HX

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
  case hole => apply HX
  case cons𝔹 HB IH =>
    apply IH; apply typing.congruence_under_ObsCtx𝔹
    apply HX; apply HB

-- Γ ⊧ e₀ ≤𝑐𝑡𝑥 e₁ : τ ≜
--   Γ ⊢ e₀ : τ ∧
--   Γ ⊢ e₁ : τ ∧
--   ∀ (⦰ ⊢ C⟦Γ ⊢ τ⟧ : τ𝕔).
--   C⟦e₀⟧⇓ → C⟦e₁⟧⇓
@[simp]
def ctx_approx (Γ : TEnv) (e₀ e₁: Expr) (τ : Ty) : Prop :=
  typing Γ 𝟚 e₀ τ ⊥ ∧
  typing Γ 𝟚 e₁ τ ⊥ ∧
    ∀ C τ𝕔, ObsCtxℂ Γ τ C ⦰ τ𝕔 →
      termination C⟦e₀⟧ →
      termination C⟦e₁⟧

lemma ctx_approx.congruence_under_ObsCtx𝔹 :
  ∀ Δ Γ τδ τγ B e₀ e₁,
    ctx_approx Δ e₀ e₁ τδ →
    ObsCtx𝔹 Δ τδ B Γ τγ →
    ctx_approx Γ B⟦e₀⟧ B⟦e₁⟧ τγ :=
  by
  intros Δ Γ τδ τγ B e₀ e₁ Hctx HB
  have ⟨Hτ₀, Hτ₁, Hctx⟩ := Hctx
  constructor; apply typing.congruence_under_ObsCtx𝔹 _ _ _ _ _ _ Hτ₀ HB
  constructor; apply typing.congruence_under_ObsCtx𝔹 _ _ _ _ _ _ Hτ₁ HB
  intros C τ𝕔 HC
  rw [ctx_comp C B, ctx_comp C B]
  apply Hctx
  apply ObsCtxℂ.cons𝔹; apply HC; apply HB

-- Δ ⊧ e₀ ≤𝑐𝑡𝑥 e₁ : τδ
-- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ
-- ————————————————————————
-- Γ ⊧ C⟦e₀⟧ ≤𝑐𝑡𝑥 C⟦e₁⟧ : τγ
lemma ctx_approx.congruence_under_ObsCtxℂ :
  ∀ Δ Γ τδ τγ C e₀ e₁,
    ctx_approx Δ e₀ e₁ τδ →
    ObsCtxℂ Δ τδ C Γ τγ →
    ctx_approx Γ C⟦e₀⟧ C⟦e₁⟧ τγ :=
  by
  intros Δ Γ τδ τγ C e₀ e₁ Hctx HC
  induction HC generalizing e₀ e₁
  case hole => apply Hctx
  case cons𝔹 HB IH =>
    apply IH
    apply ctx_approx.congruence_under_ObsCtx𝔹
    apply Hctx; apply HB

-- Γ ⊧ e₀ ≈𝑐𝑡𝑥 e₁ : τ ≜ Γ ⊧ e₀ ≤𝑐𝑡𝑥 e₁ : τ ∧ Γ ⊧ e₁ ≤𝑐𝑡𝑥 e₀ : τ
@[simp]
def ctx_equiv (Γ : TEnv) (e₀ e₁: Expr) (τ : Ty) : Prop :=
  ctx_approx Γ e₀ e₁ τ ∧ ctx_approx Γ e₁ e₀ τ
