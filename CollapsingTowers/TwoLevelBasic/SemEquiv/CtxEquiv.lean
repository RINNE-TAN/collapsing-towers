
import CollapsingTowers.TwoLevelBasic.SemEquiv.Fundamental
import CollapsingTowers.TwoLevelBasic.Deterministic
-- Γ ⊢ B⟦Δ ⊢ τδ⟧ : τγ ≜ ∀ (‖Δ‖ ⊢ X : ‖τδ‖). ‖Γ‖ ⊢ B⟦X⟧ : ‖τγ‖
inductive ObsCtx𝔹 :
  TEnv → Ty →  -- Δ ⊢ τδ
  Ctx →        -- B
  TEnv → Ty →  -- Γ ⊢ τγ
  Prop where
  | lam :
    ∀ Γ τ𝕒 τ𝕓,
      ObsCtx𝔹
        ‖(τ𝕒, .stat) :: Γ‖𝛾 ‖τ𝕓‖𝜏
        (fun X => .lam (close₀ ‖Γ‖𝛾.length X))
        ‖Γ‖𝛾 ‖.arrow τ𝕒 τ𝕓 ∅‖𝜏
  | appl₁ :
    ∀ Γ arg τ𝕒 τ𝕓,
      typing ‖Γ‖𝛾 .stat ‖arg‖ ‖τ𝕒‖𝜏 ∅ →
      ObsCtx𝔹
        ‖Γ‖𝛾 ‖.arrow τ𝕒 τ𝕓 ∅‖𝜏
        (fun X => .app₁ X ‖arg‖)
        ‖Γ‖𝛾 ‖τ𝕓‖𝜏
  | appr₁ :
    ∀ Γ f τ𝕒 τ𝕓,
      typing ‖Γ‖𝛾 .stat ‖f‖ ‖.arrow τ𝕒 τ𝕓 ∅‖𝜏 ∅ →
      ObsCtx𝔹
        ‖Γ‖𝛾 ‖τ𝕒‖𝜏
        (fun X => .app₁ ‖f‖ X)
        ‖Γ‖𝛾 ‖τ𝕓‖𝜏
  | letsl :
    ∀ Γ e τ𝕒 τ𝕓,
      closed_at ‖e‖ ‖Γ‖𝛾.length →
      typing ‖(τ𝕒, .stat) :: Γ‖𝛾 .stat (open₀ ‖Γ‖𝛾.length ‖e‖) ‖τ𝕓‖𝜏 ∅ →
      ObsCtx𝔹
        ‖Γ‖𝛾 ‖τ𝕒‖𝜏
        (fun X => .lets X ‖e‖)
        ‖Γ‖𝛾 ‖τ𝕓‖𝜏
  | letsr :
    ∀ Γ b τ𝕒 τ𝕓,
      typing ‖Γ‖𝛾 .stat ‖b‖ ‖τ𝕒‖𝜏 ∅ →
      ObsCtx𝔹
        ‖(τ𝕒, .stat) :: Γ‖𝛾 ‖τ𝕓‖𝜏
        (fun X => .lets ‖b‖ (close₀ ‖Γ‖𝛾.length X))
        ‖Γ‖𝛾 ‖τ𝕓‖𝜏

inductive ObsCtxℂ : TEnv → Ty → Ctx → TEnv → Ty → Prop where
  | hole : ∀ Γ τ, ObsCtxℂ ‖Γ‖𝛾 ‖τ‖𝜏 id ‖Γ‖𝛾 ‖τ‖𝜏
  | cons𝔹 :
    ∀ Ψ Δ Γ τψ τδ τγ C B,
      ObsCtxℂ ‖Δ‖𝛾 ‖τδ‖𝜏 C ‖Γ‖𝛾 ‖τγ‖𝜏 →
      ObsCtx𝔹 ‖Ψ‖𝛾 ‖τψ‖𝜏 B ‖Δ‖𝛾 ‖τδ‖𝜏 →
      ObsCtxℂ ‖Ψ‖𝛾 ‖τψ‖𝜏 (C ∘ B) ‖Γ‖𝛾 ‖τγ‖𝜏

theorem ObsCtx𝔹_length :
  ∀ Δ Γ τδ τγ B,
    ObsCtx𝔹 Δ τδ B Γ τγ →
    Δ.length ≥ Γ.length :=
  by
  intros Δ Γ τδ τγ B HB
  cases HB <;> simp

-- Δ ⊢ X : τδ
-- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ
-- ——————————————————
-- Γ ⊢ C⟦X⟧ : τγ
theorem typing_fill_ObsCtx𝔹 :
  ∀ Δ Γ τδ τγ B X,
    typing Δ .stat X τδ ∅ →
    ObsCtx𝔹 Δ τδ B Γ τγ →
    typing Γ .stat B⟦X⟧ τγ ∅ :=
  by
  intros Δ Γ τδ τγ B X Hτ HC
  induction HC generalizing X
  case lam =>
    apply typing.lam
    rw [← length_erase_env, open_close_id₀]
    apply Hτ; apply typing_regular; apply Hτ
    apply erase_ty_well_binding_time
    rw [close₀, ← close_closed]
    apply typing_closed _ _ _ _ _ Hτ
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
    apply erase_ty_well_binding_time
    apply Hclosed
  case letsr Hb =>
    rw [← union_pure_left ∅]
    apply typing.lets
    apply Hb
    rw [open_close_id₀]; apply Hτ
    apply typing_regular; apply Hτ
    apply erase_ty_well_binding_time
    rw [close₀, ← close_closed]
    apply typing_closed _ _ _ _ _ Hτ

-- Γ ⊢ e₀ ≈𝑐𝑡𝑥 e₁ : τ ≜
--   ∀ (∅ ⊢ C⟦Γ ⊢ τ⟧ : ℕ).
--   Γ ⊢ e₀ : τ →
--   Γ ⊢ e₁ : τ →
--   ∀ v. C⟦e₀⟧ ↦* v ↔ C⟦e₁⟧ ↦* v
@[simp]
def ctx_equiv (Γ : TEnv) (e₀ e₁: Expr) (τ : Ty) : Prop :=
  typing Γ .stat e₀ τ ∅ →
  typing Γ .stat e₁ τ ∅ →
    ∀ C, ObsCtxℂ Γ τ C [] .nat →
    ∀ v, value v →
      (stepn C⟦e₀⟧ v ↔ stepn C⟦e₁⟧ v)

theorem sem_equiv_typing_cong :
  ∀ Δ Γ τδ τγ B e₀ e₁,
    typing Δ .stat e₀ τδ ∅ →
    typing Δ .stat e₁ τδ ∅ →
    sem_equiv_typing Δ e₀ e₁ τδ →
    ObsCtx𝔹 Δ τδ B Γ τγ →
    sem_equiv_typing Γ B⟦e₀⟧ B⟦e₁⟧ τγ :=
  by
  intros Δ Γ τδ τγ B e₀ e₁ Hτ₀ Hτ₁ Hsem HB
  induction HB generalizing e₀ e₁
  case lam =>
    apply compatibility_lam
    . simp; rw [← close_closed]
      apply typing_closed _ _ _ _ _ Hτ₀
    . simp; rw [← close_closed]
      apply typing_closed _ _ _ _ _ Hτ₁
    . rw [← length_erase_env]
      rw [open_close_id₀, open_close_id₀]
      apply Hsem
      apply typing_regular; apply Hτ₁
      apply typing_regular; apply Hτ₀
  case appl₁ Harg =>
    apply compatibility_app
    . apply Hsem
    . apply fundamental _ _ _ _ _ Harg
  case appr₁ Hf =>
    apply compatibility_app
    . apply fundamental _ _ _ _ _ Hf
    . apply Hsem
  case letsl Hclosed He =>
    apply compatibility_lets
    . constructor
      . apply typing_closed; apply Hτ₀
      . apply Hclosed
    . constructor
      . apply typing_closed; apply Hτ₁
      . apply Hclosed
    . apply Hsem
    . rw [← erase_open₀_comm]
      rw [← erase_open₀_comm] at He
      apply fundamental _ _ _ _ _ He
  case letsr Hb =>
    apply compatibility_lets
    . constructor
      . apply typing_closed; apply Hb
      . simp; rw [← close_closed]
        apply typing_closed _ _ _ _ _ Hτ₀
    . constructor
      . apply typing_closed; apply Hb
      . simp; rw [← close_closed]
        apply typing_closed _ _ _ _ _ Hτ₁
    . apply fundamental _ _ _ _ _ Hb
    . rw [open_close_id₀, open_close_id₀]
      apply Hsem
      apply typing_regular; apply Hτ₁
      apply typing_regular; apply Hτ₀

-- ∅ ⊧ e₀ ≈ e₁ : τ
-- ————————————————
-- ∅ ⊢ e₀ ≈𝑐𝑡𝑥 e₁ : τ
theorem sem_soundness :
  ∀ τ e₀ e₁,
    sem_equiv_typing [] e₀ e₁ τ →
    ctx_equiv [] e₀ e₁ τ :=
  by
  generalize HEqΓ : [] = Γ
  intros τ e₀ e₁ Hsem Hτ₀ Hτ₁ C
  generalize HEqΔ : [] = Δ
  generalize HEqτδ : Ty.nat = τδ
  intros HC v Hvalue
  induction HC generalizing e₀ e₁
  case hole =>
    rw [← HEqΓ, ← HEqτδ] at Hsem
    have ⟨Hwf₀, Hwf₁, Hsem⟩ := Hsem
    have Hsem_expr := Hsem _ _ sem_equiv_env.nil
    rw [sem_equiv_expr] at Hsem_expr
    have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value⟩ := Hsem_expr
    cases v₀ <;> cases v₁ <;> simp at Hsem_value
    have Hstepv₀ := pure_stepn_impl_stepn _ _ Hstepv₀
    have Hstepv₁ := pure_stepn_impl_stepn _ _ Hstepv₁
    constructor
    . intro Hstepv
      rw [← church_rosser _ _ _ Hstepv₀ Hstepv, Hsem_value]
      apply Hstepv₁
      . apply value.lit
      . apply Hvalue
    . intro Hstepv
      rw [← church_rosser _ _ _ Hstepv₁ Hstepv, ← Hsem_value]
      apply Hstepv₀
      . apply value.lit
      . apply Hvalue
  case cons𝔹 C B HC HB IH =>
    apply IH
    rw [← HEqΓ] at HB
    have H := ObsCtx𝔹_length _ _ _ _ _ HB
    simp at H; rw [H]
    apply sem_equiv_typing_cong
    apply Hτ₀; apply Hτ₁
    apply Hsem; apply HB
    apply typing_fill_ObsCtx𝔹; apply Hτ₀; apply HB
    apply typing_fill_ObsCtx𝔹; apply Hτ₁; apply HB
    apply HEqΔ; apply HEqτδ
