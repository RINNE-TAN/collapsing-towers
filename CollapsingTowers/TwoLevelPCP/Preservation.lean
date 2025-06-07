
import CollapsingTowers.TwoLevelPCP.Typing
import CollapsingTowers.TwoLevelPCP.Shift
@[simp]
def dyn_env (Γ : TEnv) : Prop :=
  ∀ x τ 𝕊, binds x τ 𝕊 Γ -> 𝕊 = .dyn

theorem preservation_subst_strengthened :
    ∀ Γ Δ Φ v e τ𝕒 τ𝕓 φ,
      typing Γ .stat e τ𝕓 φ ->
      Γ = Δ ++ (τ𝕒, .stat) :: Φ ->
      typing Φ .stat v τ𝕒 ∅ ->
      typing (Δ ++ Φ) .stat (shiftr_at Φ.length (subst Φ.length v e)) τ𝕓 φ :=
  by
  generalize Eq𝕊 : Stage.stat = 𝕊
  intros Γ Δ Φ v e τ𝕒 τ𝕓 φ Hτe HEqΓ Hτv
  revert Δ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ𝕓 φ (H : typing Γ 𝕊 e τ𝕓 φ) =>
        ∀ (Δ : TEnv), Γ = Δ ++ (τ𝕒, 𝕊) :: Φ → typing (Δ ++ Φ) 𝕊 (shiftr_at Φ.length (subst Φ.length v e)) τ𝕓 φ)
      (fun Γ e τ𝕓 φ (H : typing_reification Γ e τ𝕓 φ) =>
        ∀ (Δ : TEnv),
          Γ = Δ ++ (τ𝕒, 𝕊) :: Φ → typing_reification (Δ ++ Φ) (shiftr_at Φ.length (subst Φ.length v e)) τ𝕓 φ)
  case fvar =>
    intros _ _ x _ Hbinds Δ HEqΓ
    admit
  case lam₁ =>
    intros _ _ _ _ _ _ _ HwellBinds Hclose IH Δ HEqΓ
    admit
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ IHf IHarg Δ HEqΓ
    constructor
    apply IHf; apply HEqΓ
    apply IHarg; apply HEqΓ
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ IHf IHarg Δ HEqΓ
    constructor
    apply IHf; apply HEqΓ
    apply IHarg; apply HEqΓ
  case lam𝕔 =>
    intros _ _ _ _ _ _ HwellBinds Hclose IH Δ HEqΓ
    admit
  case pure =>
    intros _ _ _ _ IH Δ HEqΓ
    apply typing_reification.pure
    apply IH; rw [Eq𝕊]; apply HEqΓ
  case reify =>
    intros _ _ _ _ IH Δ HEqΓ
    apply typing_reification.reify
    apply IH; rw [Eq𝕊]; apply HEqΓ
  all_goals admit

theorem preservation_head𝕄 :
    ∀ Γ e₀ e₁ τ φ,
      dyn_env Γ ->
      head𝕄 e₀ e₁ ->
      lc e₀ ->
      typing Γ .stat e₀ τ φ ->
      typing Γ .stat e₁ τ φ :=
  by
  intros Γ e₀ e₁ τ φ HdynΓ Hhead Hlc Hτ
  cases Hhead
  case lets Hvalue => admit
  all_goals admit

theorem preservation_strengthened :
    ∀ Γ e₀ e₁ τ φ₀,
      dyn_env Γ ->
      step_lvl Γ.length e₀ e₁ ->
      typing_reification Γ e₀ τ φ₀ ->
      ∃ φ₁, typing_reification Γ e₁ τ φ₁ ∧ φ₁ <= φ₀ :=
  by
  intro Γ e₀ e₁ τ φ₀
  generalize HEqlvl : Γ.length = lvl
  intro HdynΓ Hstep Hτ; cases Hstep
  case step𝕄 HM Hlc Hhead𝕄 =>
    induction HM generalizing τ Γ
    case hole =>
      exists φ₀; constructor
      . cases Hτ
        all_goals
          (next Hτ =>
              constructor
              apply preservation_head𝕄
              apply HdynΓ; apply Hhead𝕄; apply Hlc; apply Hτ)
      . rfl
    case cons𝔹 HB _ IHM => admit
    case consℝ HR HM IHM => admit
  case reflect => admit
