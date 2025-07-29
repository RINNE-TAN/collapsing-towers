import CollapsingTowers.TwoLevelBasic.SyntacticTyping.Defs
import CollapsingTowers.TwoLevelBasic.Erasure.Defs

-- Γ ⊢ B⟦Δ ⊢ τδ⟧ : τγ ≜ ∀ (‖Δ‖ ⊢ X : ‖τδ‖). ‖Γ‖ ⊢ B⟦X⟧ : ‖τγ‖
inductive ObsCtx𝔹 :
  TEnv → Ty →  -- Δ ⊢ τδ
  Ctx →        -- B
  TEnv → Ty →  -- Γ ⊢ τγ
  Prop where
  | lam :
    ∀ Γ τ𝕒 τ𝕓,
      ObsCtx𝔹
        ‖(τ𝕒, 𝟙) :: Γ‖𝛾 ‖τ𝕓‖𝜏
        (fun X => .lam ({0 ↤ ‖Γ‖𝛾.length} X))
        ‖Γ‖𝛾 ‖.arrow τ𝕒 τ𝕓 ∅‖𝜏
  | appl₁ :
    ∀ Γ arg τ𝕒 τ𝕓,
      typing ‖Γ‖𝛾 𝟙 ‖arg‖ ‖τ𝕒‖𝜏 ∅ →
      ObsCtx𝔹
        ‖Γ‖𝛾 ‖.arrow τ𝕒 τ𝕓 ∅‖𝜏
        (fun X => .app₁ X ‖arg‖)
        ‖Γ‖𝛾 ‖τ𝕓‖𝜏
  | appr₁ :
    ∀ Γ f τ𝕒 τ𝕓,
      typing ‖Γ‖𝛾 𝟙 ‖f‖ ‖.arrow τ𝕒 τ𝕓 ∅‖𝜏 ∅ →
      ObsCtx𝔹
        ‖Γ‖𝛾 ‖τ𝕒‖𝜏
        (fun X => .app₁ ‖f‖ X)
        ‖Γ‖𝛾 ‖τ𝕓‖𝜏
  | letsl :
    ∀ Γ e τ𝕒 τ𝕓,
      closed_at ‖e‖ ‖Γ‖𝛾.length →
      typing ‖(τ𝕒, 𝟙) :: Γ‖𝛾 𝟙 ({0 ↦ ‖Γ‖𝛾.length} ‖e‖) ‖τ𝕓‖𝜏 ∅ →
      ObsCtx𝔹
        ‖Γ‖𝛾 ‖τ𝕒‖𝜏
        (fun X => .lets X ‖e‖)
        ‖Γ‖𝛾 ‖τ𝕓‖𝜏
  | letsr :
    ∀ Γ b τ𝕒 τ𝕓,
      typing ‖Γ‖𝛾 𝟙 ‖b‖ ‖τ𝕒‖𝜏 ∅ →
      ObsCtx𝔹
        ‖(τ𝕒, 𝟙) :: Γ‖𝛾 ‖τ𝕓‖𝜏
        (fun X => .lets ‖b‖ ({0 ↤ ‖Γ‖𝛾.length} X))
        ‖Γ‖𝛾 ‖τ𝕓‖𝜏

inductive ObsCtxℂ : TEnv → Ty → Ctx → TEnv → Ty → Prop where
  | hole : ∀ Γ τ, ObsCtxℂ ‖Γ‖𝛾 ‖τ‖𝜏 id ‖Γ‖𝛾 ‖τ‖𝜏
  | cons𝔹 :
    ∀ Ψ Δ Γ τψ τδ τγ C B,
      ObsCtxℂ ‖Δ‖𝛾 ‖τδ‖𝜏 C ‖Γ‖𝛾 ‖τγ‖𝜏 →
      ObsCtx𝔹 ‖Ψ‖𝛾 ‖τψ‖𝜏 B ‖Δ‖𝛾 ‖τδ‖𝜏 →
      ObsCtxℂ ‖Ψ‖𝛾 ‖τψ‖𝜏 (C ∘ B) ‖Γ‖𝛾 ‖τγ‖𝜏

lemma typing.congruence_under_ObsCtx𝔹 :
  ∀ Δ Γ τδ τγ B X,
    typing Δ 𝟙 X τδ ∅ →
    ObsCtx𝔹 Δ τδ B Γ τγ →
    typing Γ 𝟙 B⟦X⟧ τγ ∅ :=
  by
  intros Δ Γ τδ τγ B X Hτ HC
  induction HC generalizing X
  case lam =>
    apply typing.lam
    rw [← env.erase.length, identity.opening_closing]
    apply Hτ; apply typing.regular; apply Hτ
    apply ty.erase.wbt
    rw [← closed.under_closing]
    apply typing.closed_at_env _ _ _ _ _ Hτ
  case appl₁ Harg =>
    rw [← union_pure_left ∅, ← union_pure_left ∅]
    apply typing.app₁
    apply Hτ; apply Harg
  case appr₁ Hf =>
    rw [← union_pure_left ∅, ← union_pure_left ∅]
    apply typing.app₁
    apply Hf; apply Hτ
  case letsl Hclosed He =>
    rw [← union_pure_left ∅]
    apply typing.lets
    apply Hτ; apply He
    apply ty.erase.wbt
    apply Hclosed
  case letsr Hb =>
    rw [← union_pure_left ∅]
    apply typing.lets
    apply Hb
    rw [identity.opening_closing]; apply Hτ
    apply typing.regular; apply Hτ
    apply ty.erase.wbt
    rw [← closed.under_closing]
    apply typing.closed_at_env _ _ _ _ _ Hτ

-- Δ ⊢ X : τδ
-- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ
-- ——————————————————
-- Γ ⊢ C⟦X⟧ : τγ
lemma typing.congruence_under_ObsCtxℂ :
  ∀ Δ Γ τδ τγ C X,
    typing Δ 𝟙 X τδ ∅ →
    ObsCtxℂ Δ τδ C Γ τγ →
    typing Γ 𝟙 C⟦X⟧ τγ ∅ :=
  by
  intros Δ Γ τδ τγ C X Hτ HC
  induction HC generalizing X
  case hole => apply Hτ
  case cons𝔹 HB IH =>
    apply IH; apply typing.congruence_under_ObsCtx𝔹
    apply Hτ; apply HB

-- Γ ⊢ e₀ ≈𝑐𝑡𝑥 e₁ : τ ≜
--   ∀ (∅ ⊢ C⟦Γ ⊢ τ⟧ : ℕ).
--   Γ ⊢ e₀ : τ →
--   Γ ⊢ e₁ : τ →
--   ∀ v. C⟦e₀⟧ ⇝* v ↔ C⟦e₁⟧ ⇝* v
@[simp]
def ctx_equiv (Γ : TEnv) (e₀ e₁: Expr) (τ : Ty) : Prop :=
  typing Γ 𝟙 e₀ τ ∅ →
  typing Γ 𝟙 e₁ τ ∅ →
    ∀ C, ObsCtxℂ Γ τ C [] .nat →
    ∀ v, value v → (
      (C⟦e₀⟧ ⇝* v) ↔ (C⟦e₁⟧ ⇝* v)
    )
