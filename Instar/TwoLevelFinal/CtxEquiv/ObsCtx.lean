import Instar.TwoLevelFinal.OperationalSemantics.Defs
import Instar.TwoLevelFinal.SyntacticTyping.Defs

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
  | binaryl₁ :
    ∀ Γ op r,
      typing Γ 𝟚 r .nat ⊥ →
      ObsCtx𝔽
        Γ .nat
        (fun X => .binary₁ op X r)
        Γ .nat
  | binaryr₁ :
    ∀ Γ op l,
      typing Γ 𝟚 l .nat ⊥ →
      ObsCtx𝔽
        Γ .nat
        (fun X => .binary₁ op l X)
        Γ .nat
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
  | alloc₁ :
    ∀ Γ,
      ObsCtx𝔽
        Γ .nat
        (fun X => .alloc₁ X)
        Γ (.ref .nat)
  | load₁ :
    ∀ Γ,
      ObsCtx𝔽
        Γ (.ref .nat)
        (fun X => .load₁ X)
        Γ .nat
  | storel₁ :
    ∀ Γ r,
      typing Γ 𝟚 r .nat ⊥ →
      ObsCtx𝔽
        Γ (.ref .nat)
        (fun X => .store₁ X r)
        Γ .unit
  | storer₁ :
    ∀ Γ l,
      typing Γ 𝟚 l (.ref .nat) ⊥ →
      ObsCtx𝔽
        Γ .nat
        (fun X => .store₁ l X)
        Γ .unit
  | fix₁ :
    ∀ Γ τ𝕒 τ𝕓,
      ObsCtx𝔽
        Γ (.arrow (.arrow τ𝕒 τ𝕓 ⊥) (.arrow τ𝕒 τ𝕓 ⊥) ⊥)
        (fun X => .fix₁ X)
        Γ (.arrow τ𝕒 τ𝕓 ⊥)
  | ifz₁ :
    ∀ Γ l r τ,
      typing Γ 𝟚 l τ ⊥ →
      typing Γ 𝟚 r τ ⊥ →
      ObsCtx𝔽
        Γ .nat
        (fun X => .ifz₁ X l r)
        Γ τ
  | ifzl₁ :
    ∀ Γ c r τ,
      typing Γ 𝟚 c .nat ⊥ →
      typing Γ 𝟚 r τ ⊥ →
      ObsCtx𝔽
        Γ τ
        (fun X => .ifz₁ c X r)
        Γ τ
  | ifzr₁ :
    ∀ Γ c l τ,
      typing Γ 𝟚 c .nat ⊥ →
      typing Γ 𝟚 l τ ⊥ →
      ObsCtx𝔽
        Γ τ
        (fun X => .ifz₁ c l X)
        Γ τ

-- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ ≜ ∀ (Δ ⊢ X : τδ). Γ ⊢ C⟦X⟧ : τγ
inductive ObsCtxℂ : TEnv → Ty → Ctx → TEnv → Ty → Prop where
  | hole : ∀ Γ τ, ObsCtxℂ Γ τ id Γ τ
  | cons𝔽 :
    ∀ Ψ Δ Γ τψ τδ τγ C F,
      ObsCtxℂ Δ τδ C Γ τγ →
      ObsCtx𝔽 Ψ τψ F Δ τδ →
      ObsCtxℂ Ψ τψ (C ∘ F) Γ τγ

lemma typing.congruence_under_ObsCtx𝔽 :
  ∀ Δ Γ τδ τγ F X,
    typing Δ 𝟚 X τδ ⊥ →
    ObsCtx𝔽 Δ τδ F Γ τγ →
    typing Γ 𝟚 F⟦X⟧ τγ ⊥ :=
  by
  intros Δ Γ τδ τγ F X HX HC
  induction HC generalizing X
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
  case alloc₁ =>
    apply typing.alloc₁
    apply HX
  case load₁ =>
    apply typing.load₁
    apply HX
  case storel₁ Hr =>
    rw [← Effect.union_pure ⊥]
    apply typing.store₁; apply HX; apply Hr
  case storer₁ Hl =>
    rw [← Effect.union_pure ⊥]
    apply typing.store₁; apply Hl; apply HX
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
  case cons𝔽 HF IH =>
    apply IH; apply typing.congruence_under_ObsCtx𝔽
    apply HX; apply HF

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

-- Γ ⊧ e₀ ≃𝑐𝑡𝑥 e₁ : τ ≜ Γ ⊧ e₀ ≤𝑐𝑡𝑥 e₁ : τ ∧ Γ ⊧ e₁ ≤𝑐𝑡𝑥 e₀ : τ
@[simp]
def ctx_equiv (Γ : TEnv) (e₀ e₁: Expr) (τ : Ty) : Prop :=
  ctx_approx Γ e₀ e₁ τ ∧ ctx_approx Γ e₁ e₀ τ
