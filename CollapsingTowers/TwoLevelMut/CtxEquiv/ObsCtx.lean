import CollapsingTowers.TwoLevelMut.OperationalSemantics.Defs
import CollapsingTowers.TwoLevelMut.SyntacticTyping.Defs

inductive ObsCtx𝔹 : TEnv → Ty → MEffects → Ctx → TEnv → Ty → MEffects → Prop where
  | lam :
    ∀ Γ τ𝕒 τ𝕓 ω,
      wbt 𝟚 τ𝕒 →
      ObsCtx𝔹
        ((τ𝕒, 𝟚) :: Γ) τ𝕓 ω
        (fun X => .lam ({0 ↤ Γ.length} X))
        Γ (.arrow τ𝕒 τ𝕓 ⊥ ω) ∅
  | appl₁ :
    ∀ Γ arg τ𝕒 τ𝕓 ω₀ ω₁ ω₂,
      typing ϵ Γ 𝟚 arg τ𝕒 ⊥ ω₂ →
      ObsCtx𝔹
        Γ (.arrow τ𝕒 τ𝕓 ⊥ ω₀) ω₁
        (fun X => .app₁ X arg)
        Γ τ𝕓 (ω₀ ∪ ω₁ ∪ ω₂)
  | appr₁ :
    ∀ Γ f τ𝕒 τ𝕓 ω₀ ω₁ ω₂,
      typing ϵ Γ 𝟚 f (.arrow τ𝕒 τ𝕓 ⊥ ω₀) ⊥ ω₁ →
      ObsCtx𝔹
        Γ τ𝕒 ω₂
        (fun X => .app₁ f X)
        Γ τ𝕓 (ω₀ ∪ ω₁ ∪ ω₂)
  | letsl :
    ∀ Γ e τ𝕒 τ𝕓 ω₀ ω₁,
      closed_at e Γ.length →
      typing ϵ ((τ𝕒, 𝟚) :: Γ) 𝟚 ({0 ↦ Γ.length} e) τ𝕓 ⊥ ω₁ →
      ObsCtx𝔹
        Γ τ𝕒 ω₀
        (fun X => .lets X e)
        Γ τ𝕓 (ω₀ ∪ ω₁)
  | letsr :
    ∀ Γ b τ𝕒 τ𝕓 ω₀ ω₁,
      typing ϵ Γ 𝟚 b τ𝕒 ⊥ ω₀ →
      ObsCtx𝔹
        ((τ𝕒, 𝟚) :: Γ) τ𝕓 ω₁
        (fun X => .lets b ({0 ↤ Γ.length} X))
        Γ τ𝕓 (ω₀ ∪ ω₁)
  | alloc₁ :
    ∀ Γ ω,
      ObsCtx𝔹
        Γ .nat ω
        (fun X => .alloc₁ X)
        Γ (.ref .nat) (ω ∪ { .init 𝟚 })
  | load₁ :
    ∀ Γ ω,
      ObsCtx𝔹
        Γ (.ref .nat) ω
        (fun X => .load₁ X)
        Γ .nat (ω ∪ { .read 𝟚 })
  | storel₁ :
    ∀ Γ r ω₀ ω₁,
      typing ϵ Γ 𝟚 r .nat ⊥ ω₁ →
      ObsCtx𝔹
        Γ (.ref .nat) ω₀
        (fun X => .store₁ X r)
        Γ .unit (ω₀ ∪ ω₁ ∪ { .write 𝟚 })
  | storer₁ :
    ∀ Γ l ω₀ ω₁,
      typing ϵ Γ 𝟚 l (.ref .nat) ⊥ ω₀ →
      ObsCtx𝔹
        Γ .nat ω₁
        (fun X => .store₁ l X)
        Γ .unit (ω₀ ∪ ω₁ ∪ { .write 𝟚 })

-- Γ ⊢ C⟦Δ ⊢ τδ ! ωδ⟧ : τγ ! ωγ ≜ ∀ (Δ ⊢ X : τδ ! ωδ). Γ ⊢ C⟦X⟧ : τγ ! ωγ
inductive ObsCtxℂ : TEnv → Ty → MEffects → Ctx → TEnv → Ty → MEffects → Prop where
  | hole : ∀ Γ τ ω, ObsCtxℂ Γ τ ω id Γ τ ω
  | cons𝔹 :
    ∀ Ψ Δ Γ τψ τδ τγ ωψ ωδ ωγ C B,
      ObsCtxℂ Δ τδ ωδ C Γ τγ ωγ →
      ObsCtx𝔹 Ψ τψ ωψ B Δ τδ ωδ →
      ObsCtxℂ Ψ τψ ωψ (C ∘ B) Γ τγ ωγ

lemma typing.congruence_under_ObsCtx𝔹 :
  ∀ Δ Γ τδ τγ ωδ ωγ B X,
    typing ϵ Δ 𝟚 X τδ ⊥ ωδ →
    ObsCtx𝔹 Δ τδ ωδ B Γ τγ ωγ →
    typing ϵ Γ 𝟚 B⟦X⟧ τγ ⊥ ωγ :=
  by
  intros Δ Γ τδ τγ ωδ ωγ B X HX HB
  cases HB
  case lam Hwbt =>
    apply typing.lam
    . rw [identity.opening_closing]
      apply HX; apply typing.regular; apply HX
    . apply Hwbt
    . rw [← closed.under_closing]
      apply typing.closed_at_env _ _ _ _ _ _ _ HX
  case appl₁ Harg =>
    rw [← REffects.union_pure ⊥, ← REffects.union_pure (⊥ ∪ ⊥)]
    apply typing.app₁; apply HX; apply Harg
  case appr₁ Hf =>
    rw [← REffects.union_pure ⊥, ← REffects.union_pure (⊥ ∪ ⊥)]
    apply typing.app₁; apply Hf; apply HX
  case letsl Hclosed He =>
    rw [← REffects.union_pure ⊥]
    apply typing.lets
    . apply HX
    . apply He
    . have ⟨Hwbt, _, _⟩ := typing.dynamic_impl_pure _ _ _ _ _ _ HX
      apply Hwbt
    . apply Hclosed
  case letsr Hb =>
    rw [← REffects.union_pure ⊥]
    apply typing.lets
    . apply Hb
    . rw [identity.opening_closing]; apply HX
      apply typing.regular; apply HX
    . have ⟨Hwbt, _, _⟩ := typing.dynamic_impl_pure _ _ _ _ _ _ Hb
      apply Hwbt
    . rw [← closed.under_closing]
      apply typing.closed_at_env _ _ _ _ _ _ _ HX
  case alloc₁ =>
    apply typing.alloc₁
    apply HX
  case load₁ =>
    apply typing.load₁
    apply HX
  case storel₁ Hr =>
    rw [← REffects.union_pure ⊥]
    apply typing.store₁; apply HX; apply Hr
  case storer₁ Hl =>
    rw [← REffects.union_pure ⊥]
    apply typing.store₁; apply Hl; apply HX

-- Δ ⊢ X : τδ
-- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ
-- ——————————————————
-- Γ ⊢ C⟦X⟧ : τγ
lemma typing.congruence_under_ObsCtxℂ :
  ∀ Δ Γ τδ τγ ωδ ωγ B X,
    typing ϵ Δ 𝟚 X τδ ⊥ ωδ →
    ObsCtxℂ Δ τδ ωδ B Γ τγ ωγ →
    typing ϵ Γ 𝟚 B⟦X⟧ τγ ⊥ ωγ :=
  by
  intros Δ Γ τδ τγ ωδ ωγ C X HX HC
  induction HC generalizing X
  case hole => apply HX
  case cons𝔹 HB IH =>
    apply IH; apply typing.congruence_under_ObsCtx𝔹
    apply HX; apply HB

-- Γ ⊧ e₀ ≈𝑐𝑡𝑥 e₁ : τ ! ω ≜
--   Γ ⊢ e₀ : τ ！ω ∧
--   Γ ⊢ e₁ : τ ！ω ∧
--   ∀ (⦰ ⊢ C⟦Γ ⊢ τ ！ω⟧ : ℕ ! ω𝕔).
--   ∃ σ₀ σ₁ v.
--     ⟨ϵ, C⟦e₀⟧⟩ ⇝* ⟨σ₀, v⟩ ∧
--     ⟨ϵ, C⟦e₁⟧⟩ ⇝* ⟨σ₁, v⟩
@[simp]
def ctx_equiv (Γ : TEnv) (e₀ e₁: Expr) (τ : Ty) (ω : MEffects) : Prop :=
  typing ϵ Γ 𝟚 e₀ τ ⊥ ω ∧
  typing ϵ Γ 𝟚 e₁ τ ⊥ ω ∧
    ∀ C ω𝕔, ObsCtxℂ Γ τ ω C ⦰ .nat ω𝕔 →
    ∃ σ₀ σ₁ v,
      value v ∧
      (⟨ϵ, C⟦e₀⟧⟩ ⇝* ⟨σ₀, v⟩) ∧
      (⟨ϵ, C⟦e₁⟧⟩ ⇝* ⟨σ₁, v⟩)
