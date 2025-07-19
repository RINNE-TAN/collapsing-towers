
import CollapsingTowers.TwoLevelBasic.SemEquiv.Fundamental
-- Γ ⊢ B⟦Δ ⊢ τδ⟧ : τγ ≜ ∀ (Δ ⊢ e : τδ). Γ ⊢ B⟦e⟧ : τγ
inductive ObsCtx𝔹 :
  TEnv → Ty →  -- Δ ⊢ τδ
  Ctx →        -- C
  TEnv → Ty →  -- Γ ⊢ τγ
  Prop where
  | lam :
    ∀ Γ τ𝕒 τ𝕓,
      well_binding_time .stat τ𝕒 →
      ObsCtx𝔹
        ((τ𝕒, .stat) :: Γ) τ𝕓
        (fun X => .lam (close₀ Γ.length X))
        Γ (.arrow τ𝕒 τ𝕓 ∅)
  | appl₁ :
    ∀ Γ arg τ𝕒 τ𝕓,
      typing Γ .stat arg τ𝕒 ∅ →
      ObsCtx𝔹
        Γ (.arrow τ𝕒 τ𝕓 ∅)
        (fun X => .app₁ X arg)
        Γ τ𝕓
  | appr₁ :
    ∀ Γ f τ𝕒 τ𝕓,
      typing Γ .stat f (.arrow τ𝕒 τ𝕓 ∅) ∅ →
      ObsCtx𝔹
        Γ τ𝕒
        (fun X => .app₁ f X)
        Γ τ𝕓
  | letsl :
    ∀ Γ e τ𝕒 τ𝕓,
      well_binding_time .stat τ𝕒 →
      closed_at e Γ.length →
      typing ((τ𝕒, .stat) :: Γ) .stat (open₀ Γ.length e) τ𝕓 ∅ →
      ObsCtx𝔹
        Γ τ𝕒
        (fun X => .lets X e)
        Γ τ𝕓
  | letsr :
    ∀ Γ b τ𝕒 τ𝕓,
      well_binding_time .stat τ𝕒 →
      typing Γ .stat b τ𝕒 ∅ →
      ObsCtx𝔹
        ((τ𝕒, .stat) :: Γ) τ𝕓
        (fun X => .lets b (close₀ Γ.length X))
        Γ τ𝕓

inductive ObsCtxℂ : TEnv → Ty → Ctx → TEnv → Ty → Prop where
  | hole : ∀ Γ τ, ObsCtxℂ Γ τ id Γ τ
  -- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ
  -- Δ ⊢ B⟦Ψ ⊢ τψ⟧ : τδ
  -- ———————————————————————
  -- Γ ⊢ (C ∘ B)⟦Ψ ⊢ τψ⟧ : τγ
  | cons𝔹 :
    ∀ Ψ Δ Γ τψ τδ τγ C B,
      ObsCtxℂ Δ τδ C Γ τγ →
      ObsCtx𝔹 Ψ τψ B Δ τδ →
      ObsCtxℂ Ψ τψ (C ∘ B) Γ τγ

-- Δ ⊢ e : τδ
-- Γ ⊢ B⟦Δ ⊢ τδ⟧ : τγ
-- ——————————————————
-- Γ ⊢ B⟦e⟧ : τγ
theorem typing_fill_ObsCtx𝔹 :
  ∀ Δ Γ τδ τγ B e,
    typing Δ .stat e τδ ∅ →
    ObsCtx𝔹 Δ τδ B Γ τγ →
    typing Γ .stat B⟦e⟧ τγ ∅ :=
  by
  intros Δ Γ τδ τγ B e HX HB
  cases HB
  case lam HwellBinds =>
    apply typing.lam
    rw [open_close_id₀]; apply HX
    apply typing_regular; apply HX
    apply HwellBinds
    rw [close₀, ← close_closed]
    apply typing_closed _ _ _ _ _ HX
  case appl₁ Harg =>
    rw [← union_pure_left ∅, ← union_pure_left ∅]
    apply typing.app₁
    apply HX; apply Harg
  case appr₁ Hf =>
    rw [← union_pure_left ∅, ← union_pure_left ∅]
    apply typing.app₁
    apply Hf; apply HX
  case letsl Hclosed HwellBinds He =>
    rw [← union_pure_left ∅]
    apply typing.lets
    apply HX; apply He
    apply HwellBinds; apply Hclosed
  case letsr HwellBinds Hb =>
    rw [← union_pure_left ∅]
    apply typing.lets
    apply Hb
    rw [open_close_id₀]; apply HX
    apply typing_regular; apply HX
    apply HwellBinds
    rw [close₀, ← close_closed]
    apply typing_closed _ _ _ _ _ HX

-- Δ ⊢ e : τδ
-- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ
-- ——————————————————
-- Γ ⊢ C⟦e⟧ : τγ
theorem typing_fill_ObsCtxℂ :
  ∀ Δ Γ τδ τγ C e,
    typing Δ .stat e τδ ∅ →
    ObsCtxℂ Δ τδ C Γ τγ →
    typing Γ .stat C⟦e⟧ τγ ∅ :=
  by
  intros Δ Γ τδ τγ C e Hτ HC
  induction HC generalizing e
  case hole => apply Hτ
  case cons𝔹 C B HC HB IH =>
    apply IH; apply typing_fill_ObsCtx𝔹
    apply Hτ; apply HB

@[pp_using_anonymous_constructor]
structure TypedExpr (Γ : TEnv) (τ : Ty) where
  mk ::
  expr : Expr
  Hτ : typing Γ .stat expr τ ∅

-- e₀ ≈ e₁ ≜ ∀ (∅ ⊢ C⟦Γ ⊢ τ⟧ : nat). ∀ v. C⟦e₀⟧ ↦* v ↔ C⟦e₁⟧ ↦* v
@[simp]
def obs_equiv {Γ : TEnv} {τ : Ty} (e₀ e₁ : TypedExpr Γ τ) : Prop :=
  ∀ C,
    ObsCtxℂ Γ τ C [] .nat →
    ∀ v,
      stepn C⟦e₀.expr⟧ v ↔ stepn C⟦e₁.expr⟧ v

theorem obs_equiv_symm :
  ∀ {Γ : TEnv} {τ : Ty} (e₀ e₁ : TypedExpr Γ τ),
    obs_equiv e₀ e₁ →
    obs_equiv e₁ e₀ :=
  by
  intros Γ τ e₀ e₁ HObsEq C HC v
  rw [← HObsEq]; apply HC

theorem obs_equiv_trans :
  ∀ {Γ : TEnv} {τ : Ty} (e₀ e₁ e₂ : TypedExpr Γ τ),
    obs_equiv e₀ e₁ →
    obs_equiv e₁ e₂ →
    obs_equiv e₀ e₂ :=
  by
  intros Γ τ e₀ e₁ e₂ HObsEq₀ HObsEq₁ C HC v
  rw [HObsEq₀, HObsEq₁]; apply HC; apply HC

theorem sem_equiv_typing_cong :
  ∀ Δ Γ τδ τγ C e₀ e₁,
    typing Δ .stat e₀ τδ ∅ →
    typing Δ .stat e₁ τδ ∅ →
    sem_equiv_typing Δ e₀ e₁ τδ →
    ObsCtx𝔹 Δ τδ C Γ τγ →
    sem_equiv_typing Γ C⟦e₀⟧ C⟦e₁⟧ τγ :=
  by
  intros Δ Γ τδ τγ C e₀ e₁ Hτ₀ Hτ₁ Hsem HB
  cases HB
  case lam HwellBinds =>
    apply compatibility_lam
    . simp [close₀, ← close_closed]
      apply typing_closed _ _ _ _ _ Hτ₀
    . simp [close₀, ← close_closed]
      apply typing_closed _ _ _ _ _ Hτ₁
    . rw [open_close_id₀, open_close_id₀]
      apply Hsem
      apply typing_regular; apply Hτ₁
      apply typing_regular; apply Hτ₀
  case appl₁ Harg =>
    apply compatibility_app
    apply Hsem
    admit
  case appr₁ Hf =>
    admit
  case letsl Hclosed HwellBinds He =>
    admit
  case letsr HwellBinds Hb =>
    admit

-- Γ ⊢ e₀ : τ
-- Γ ⊢ e₁ : τ
-- Γ ⊧ e₀ ≈ e₁ : τ
-- ————————————————
-- e₀ ≈ e₁
theorem sem_soundness :
  ∀ Γ τ e₀ e₁,
    (Hτ₀ : typing Γ .stat e₀ τ ∅) →
    (Hτ₁ : typing Γ .stat e₁ τ ∅) →
    sem_equiv_typing Γ e₀ e₁ τ →
    obs_equiv ⟨e₀, Hτ₀⟩ ⟨e₁, Hτ₁⟩ :=
  by
  intros Γ τ e₀ e₁ Hτ₀ Hτ₁ Hsem C
  generalize HEqΔ : [] = Δ
  generalize HEqτδ : Ty.nat = τδ
  intros HC v
  induction HC generalizing e₀ e₁
  case hole => admit
  case cons𝔹 C B HC HB IH =>
    apply IH
    apply typing_fill_ObsCtx𝔹; apply Hτ₀; apply HB
    apply typing_fill_ObsCtx𝔹; apply Hτ₁; apply HB
    apply sem_equiv_typing_cong
    apply Hτ₀; apply Hτ₁
    apply Hsem; apply HB
    apply HEqΔ; apply HEqτδ
