import Instar.TwoLevelMut.OperationalSemantics.Defs
import Instar.TwoLevelMut.SyntacticTyping.Defs

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

-- Γ ⊧ e₀ ≃𝑐𝑡𝑥 e₁ : τ ≜
--   Γ ⊢ e₀ : τ ∧
--   Γ ⊢ e₁ : τ ∧
--   ∀ (⦰ ⊢ C⟦Γ ⊢ τ⟧ : ℕ).
--   ∃ σ₀ σ₁ v.
--     ⟨ϵ, C⟦e₀⟧⟩ ⭢* ⟨σ₀, v⟩ ∧
--     ⟨ϵ, C⟦e₁⟧⟩ ⭢* ⟨σ₁, v⟩
@[simp]
def ctx_equiv (Γ : TEnv) (e₀ e₁: Expr) (τ : Ty) : Prop :=
  typing Γ 𝟚 e₀ τ ⊥ ∧
  typing Γ 𝟚 e₁ τ ⊥ ∧
    ∀ C, ObsCtxℂ Γ τ C ⦰ .nat →
    ∃ σ₀ σ₁ v,
      value v ∧
      (⟨ϵ, C⟦e₀⟧⟩ ⭢* ⟨σ₀, v⟩) ∧
      (⟨ϵ, C⟦e₁⟧⟩ ⭢* ⟨σ₁, v⟩)
