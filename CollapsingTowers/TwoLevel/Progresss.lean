
import CollapsingTowers.TwoLevel.Typing
@[simp]
def env_wfty₁ : TEnv -> Prop
  | [] => true
  | τ :: τs => wfty₁ τ /\ env_wfty₁ τs

theorem ctx_comp : (f g : Ctx) -> ∀ e, f (g e) = (f ∘ g) e := by simp

theorem ctx_swap : (f : Ctx) -> ∀ e, f (id e) = id (f e) := by simp

theorem step𝔹 : ∀ lvl B e₀ e₁, ctx𝔹 B -> step_lvl lvl e₀ e₁ -> ∃ e₂, step_lvl lvl (B e₀) e₂ :=
  by
  intros lvl B e₀ e₁ HB Hstep
  cases Hstep with
  | step𝕄 M _ _ HM Hlc Hhead =>
    rw [ctx_comp B M]
    constructor; apply step_lvl.step𝕄
    apply ctx𝕄.cons𝔹; apply HB; apply HM
    apply Hlc; apply Hhead
  | reflect P E _ HP HE Hlc =>
    cases HP with
    | hole =>
      constructor
      rw [ctx_swap B, ctx_comp B E]
      apply step_lvl.reflect
      apply ctxℙℚ.hole
      apply ctx𝔼.cons𝔹
      apply HB; apply HE; apply Hlc
    | cons𝔹 _ _ IHB HPQ =>
      constructor
      rw [ctx_comp B]
      apply step_lvl.reflect
      apply ctxℙℚ.cons𝔹; apply HB
      apply ctxℙℚ.cons𝔹; apply IHB
      apply HPQ; apply HE; apply Hlc
    | consℝ _ _ HR HPQ =>
      constructor
      rw [ctx_comp B]
      apply step_lvl.reflect
      apply ctxℙℚ.cons𝔹; apply HB
      apply ctxℙℚ.consℝ; apply HR
      apply HPQ; apply HE; apply Hlc

theorem stepℝ : ∀ lvl R e₀ e₁, ctxℝ lvl R -> step_lvl (lvl + 1) e₀ e₁ -> step_lvl lvl (R e₀) (R e₁) :=
  by
  intros lvl R e₀ e₁ HR Hstep
  cases Hstep with
  | step𝕄 M _ _ HM Hlc Hhead =>
    repeat rw [ctx_comp R M]
    apply step_lvl.step𝕄
    apply ctx𝕄.consℝ; apply HR; apply HM
    apply Hlc; apply Hhead
  | reflect P _ _ HP HE Hlc =>
    repeat rw [ctx_comp R P]
    apply step_lvl.reflect
    apply ctxℙℚ.consℝ; apply HR; apply HP
    apply HE; apply Hlc

theorem progress_rep :
    ∀ Γ e₀ τ, typing Γ e₀ τ -> env_wfty₁ Γ -> wfty₂ τ -> value e₀ \/ (∃ e₁, step_lvl Γ.length e₀ e₁) :=
  by
  intros Γ e₀ τ
  intros Hτ HwftyΓ Hwfty
  induction Hτ with
  | fvar _ _ _ Hbinds => admit
  | lam₁ => admit
  | lam₂ _ _ _ _ Hτe =>
    right
    constructor
    apply step_lvl.step𝕄 _ _ _ ctx𝕄.hole
    simp; apply open_closedb; apply typing_regular; apply Hτe
    apply head𝕄.lam₂
  | app₁ _ _ _ _ _ Hf Harg IHf IHarg =>
    right
    simp at IHf
    admit
  | app₂ _ _ _ _ _ Hf Harg IHf IHarg =>
    right
    simp at IHf IHarg
    admit
  | lam𝕔 Γ e _ _ Hτe Hclose IH =>
    right
    rw [← close_open_id₀ e Γ.length]
    generalize HEqe : open₀ Γ.length e = e𝕠
    rw [HEqe] at IH Hτe
    simp at IH Hwfty
    cases IH Hwfty.left HwftyΓ Hwfty.right with
    | inl Hvalue =>
      admit
    | inr Hstep =>
      have ⟨_, Hstep⟩ := Hstep
      constructor
      apply stepℝ _ _ _ _ ctxℝ.lam𝕔
      apply Hstep
    apply Hclose
  | _ => admit

theorem progress : ∀ e₀ τ, typing [] e₀ τ -> wfty τ -> value e₀ \/ ∃ e₁, step e₀ e₁ := by admit
