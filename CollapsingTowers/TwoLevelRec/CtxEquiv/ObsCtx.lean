import CollapsingTowers.TwoLevelRec.SyntacticTyping.Defs

-- Γ ⊢ B⟦Δ ⊢ τδ⟧ : τγ ≜ ∀ (Δ ⊢ X : τδ). Γ ⊢ B⟦X⟧ : τγ
inductive ObsCtx𝔹 :
  TEnv → Ty →  -- Δ ⊢ τδ
  Ctx →        -- B
  TEnv → Ty →  -- Γ ⊢ τγ
  Prop where
  | lam :
    ∀ Γ τ𝕒 τ𝕓,
      wbt 𝟚 τ𝕒 →
      ObsCtx𝔹
        ((τ𝕒, 𝟚) :: Γ) τ𝕓
        (fun X => .lam ({0 ↤ Γ.length} X))
        Γ (.arrow τ𝕒 τ𝕓 ∅)
  | appl₁ :
    ∀ Γ arg τ𝕒 τ𝕓,
      typing Γ 𝟚 arg τ𝕒 ∅ →
      ObsCtx𝔹
        Γ (.arrow τ𝕒 τ𝕓 ∅)
        (fun X => .app₁ X arg)
        Γ τ𝕓
  | appr₁ :
    ∀ Γ f τ𝕒 τ𝕓,
      typing Γ 𝟚 f (.arrow τ𝕒 τ𝕓 ∅) ∅ →
      ObsCtx𝔹
        Γ τ𝕒
        (fun X => .app₁ f X)
        Γ τ𝕓
  | letsl :
    ∀ Γ e τ𝕒 τ𝕓,
      closed_at e Γ.length →
      typing ((τ𝕒, 𝟚) :: Γ) 𝟚 ({0 ↦ Γ.length} e) τ𝕓 ∅ →
      ObsCtx𝔹
        Γ τ𝕒
        (fun X => .lets X e)
        Γ τ𝕓
  | letsr :
    ∀ Γ b τ𝕒 τ𝕓,
      typing Γ 𝟚 b τ𝕒 ∅ →
      ObsCtx𝔹
        ((τ𝕒, 𝟚) :: Γ) τ𝕓
        (fun X => .lets b ({0 ↤ Γ.length} X))
        Γ τ𝕓
  | fix₁ :
    ∀ Γ τ𝕒 τ𝕓,
      ObsCtx𝔹
        Γ (.arrow (.arrow τ𝕒 τ𝕓 ∅) (.arrow τ𝕒 τ𝕓 ∅) ∅)
        (fun X => .fix₁ X)
        Γ (.arrow τ𝕒 τ𝕓 ∅)

inductive ObsCtxℂ : TEnv → Ty → Ctx → TEnv → Ty → Prop where
  | hole : ∀ Γ τ, ObsCtxℂ Γ τ id Γ τ
  | cons𝔹 :
    ∀ Ψ Δ Γ τψ τδ τγ C B,
      ObsCtxℂ Δ τδ C Γ τγ →
      ObsCtx𝔹 Ψ τψ B Δ τδ →
      ObsCtxℂ Ψ τψ (C ∘ B) Γ τγ

lemma typing.congruence_under_ObsCtx𝔹 :
  ∀ Δ Γ τδ τγ B X,
    typing Δ 𝟚 X τδ ∅ →
    ObsCtx𝔹 Δ τδ B Γ τγ →
    typing Γ 𝟚 B⟦X⟧ τγ ∅ :=
  by
  intros Δ Γ τδ τγ B X Hτ HC
  induction HC generalizing X
  case lam Hwbt =>
    apply typing.lam
    . rw [identity.opening_closing]
      apply Hτ; apply typing.regular; apply Hτ
    . apply Hwbt
    . rw [← closed.under_closing]
      apply typing.closed_at_env _ _ _ _ _ Hτ
  case appl₁ Harg =>
    rw [← union_pure_left ∅, ← union_pure_left ∅]
    apply typing.app₁
    . apply Hτ
    . apply Harg
  case appr₁ Hf =>
    rw [← union_pure_left ∅, ← union_pure_left ∅]
    apply typing.app₁
    . apply Hf
    . apply Hτ
  case letsl Hclosed He =>
    rw [← union_pure_left ∅]
    apply typing.lets
    . apply Hτ
    . apply He
    . have ⟨Hwbt, _⟩ := typing.wbt_pure_at_dyn _ _ _ _ Hτ
      apply Hwbt
    . apply Hclosed
  case letsr Hb =>
    rw [← union_pure_left ∅]
    apply typing.lets
    . apply Hb
    . rw [identity.opening_closing]; apply Hτ
      apply typing.regular; apply Hτ
    . have ⟨Hwbt, _⟩ := typing.wbt_pure_at_dyn _ _ _ _ Hb
      apply Hwbt
    . rw [← closed.under_closing]
      apply typing.closed_at_env _ _ _ _ _ Hτ
  case fix₁ =>
    apply typing.fix₁
    simp; rfl; apply Hτ

-- Δ ⊢ X : τδ
-- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ
-- ——————————————————
-- Γ ⊢ C⟦X⟧ : τγ
lemma typing.congruence_under_ObsCtxℂ :
  ∀ Δ Γ τδ τγ C X,
    typing Δ 𝟚 X τδ ∅ →
    ObsCtxℂ Δ τδ C Γ τγ →
    typing Γ 𝟚 C⟦X⟧ τγ ∅ :=
  by
  intros Δ Γ τδ τγ C X Hτ HC
  induction HC generalizing X
  case hole => apply Hτ
  case cons𝔹 HB IH =>
    apply IH; apply typing.congruence_under_ObsCtx𝔹
    apply Hτ; apply HB

-- e₁⇓ ≜ ∃ v, e ⇝* v
@[simp]
def termination (e : Expr) : Prop :=
  ∃ v, value v ∧ e ⇝* v

-- Γ ⊢ e₀ ≤𝑐𝑡𝑥 e₁ : τ ≜
--   Γ ⊢ e₀ : τ →
--   Γ ⊢ e₁ : τ →
--   ∀ (∅ ⊢ C⟦Γ ⊢ τ⟧ : τ𝕔).
--   C⟦e₀⟧⇓ → C⟦e₁⟧⇓
@[simp]
def ctx_approx (Γ : TEnv) (e₀ e₁: Expr) (τ : Ty) : Prop :=
  typing Γ 𝟚 e₀ τ ∅ →
  typing Γ 𝟚 e₁ τ ∅ →
    ∀ C τ𝕔, ObsCtxℂ Γ τ C [] τ𝕔 →
      termination C⟦e₀⟧ →
      termination C⟦e₁⟧

-- Γ ⊢ e₀ ≈𝑐𝑡𝑥 e₁ : τ ≜ Γ ⊢ e₀ ≤𝑐𝑡𝑥 e₁ : τ ∧ Γ ⊢ e₁ ≤𝑐𝑡𝑥 e₀ : τ
@[simp]
def ctx_equiv (Γ : TEnv) (e₀ e₁: Expr) (τ : Ty) : Prop :=
  ctx_approx Γ e₀ e₁ τ ∧ ctx_approx Γ e₁ e₀ τ
