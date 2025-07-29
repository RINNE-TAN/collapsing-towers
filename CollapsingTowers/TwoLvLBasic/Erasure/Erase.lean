import CollapsingTowers.TwoLvLBasic.SyntacticTyping.Defs

@[simp]
def ty.erase : Ty → Ty
  | .nat => .nat
  | .arrow τa τb _ => .arrow (erase τa) (erase τb) ∅
  | .fragment τ => erase τ
  | .rep τ => erase τ

notation:max "‖" τ "‖𝜏" => ty.erase τ

@[simp]
def env.erase : TEnv → TEnv
  | [] => []
  | (τ, _) :: Γ => (‖τ‖𝜏, 𝟙) :: erase Γ

notation:max "‖" Γ "‖𝛾" => env.erase Γ

lemma ty.erase.wbt : ∀ 𝕊 τ, wbt 𝕊 ‖τ‖𝜏 :=
  by
  intros 𝕊 τ
  induction τ
  case nat => cases 𝕊 <;> simp
  case arrow IH₀ IH₁ =>
    cases 𝕊
    case stat =>
      constructor; apply IH₀; apply IH₁
    case dyn =>
      constructor; rfl
      constructor; apply IH₀; apply IH₁
  case fragment IH => apply IH
  case rep IH => apply IH

lemma env.erase.length : ∀ Γ, Γ.length = ‖Γ‖𝛾.length :=
  by
  intros Γ
  induction Γ
  case nil => rfl
  case cons IH => simp; apply IH

lemma env.erase.binds : ∀ x τ 𝕊 Γ, binds x (τ, 𝕊) Γ → binds x (‖τ‖𝜏, 𝟙) ‖Γ‖𝛾 :=
  by
  intros x τ 𝕊 Γ Hbinds
  induction Γ
  case nil => nomatch Hbinds
  case cons tails IH =>
    by_cases HEq : tails.length = x
    . simp [if_pos HEq] at Hbinds
      simp [← env.erase.length, if_pos HEq, Hbinds]
    . simp [if_neg HEq] at Hbinds
      simp [← env.erase.length, if_neg HEq]
      apply IH; apply Hbinds

lemma identity.ty.erase_erase : ∀ τ, ‖‖τ‖𝜏‖𝜏 = ‖τ‖𝜏 :=
  by
  intros τ
  induction τ
  case nat => simp
  case arrow IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply IH₁
  case fragment IH => apply IH
  case rep IH => apply IH

lemma identity.env.erase_erase : ∀ Γ, ‖‖Γ‖𝛾‖𝛾 = ‖Γ‖𝛾 :=
  by
  intros Γ
  induction Γ
  case nil => simp
  case cons IH =>
    simp; constructor
    apply identity.ty.erase_erase; apply IH

lemma identity.erase_typing_dyn : ∀ Γ e τ φ, typing Γ 𝟚 e τ φ → ‖e‖ = e :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Γ e τ φ Hτ
  revert HEq𝕊
  apply @typing.rec
    (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => 𝟚 = 𝕊 → ‖e‖ = e)
    (fun Γ e τ φ (H : typing_reification Γ e τ φ) => true)
  <;> (try intros; assumption)
  <;> (try intros; contradiction)
  <;> (try intros; simp)
  case lam Γ _ e _ _ _ _ _ Hclosed IHe HEq𝕊 =>
    rw [← identity.closing_opening _ ‖e‖, ← comm.erase_opening]
    rw [IHe, identity.closing_opening]
    apply Hclosed; apply HEq𝕊
    rw [← closed.under_erase]; apply Hclosed
  case app₁ IHf IHarg HEq𝕊 =>
    constructor
    apply IHf; apply HEq𝕊
    apply IHarg; apply HEq𝕊
  case lets e _ _ _ _ _ _ _ Hclosed IHb IHe HEq𝕊 =>
    constructor
    apply IHb; apply HEq𝕊
    rw [← identity.closing_opening _ ‖e‖, ← comm.erase_opening]
    rw [IHe, identity.closing_opening]
    apply Hclosed; apply HEq𝕊
    rw [← closed.under_erase]; apply Hclosed

lemma identity.ty.erase_wbt_dyn : ∀ τ, wbt 𝟚 τ → ‖τ‖𝜏 = τ :=
  by
  intros τ HwellBinds
  induction τ
  case nat => rfl
  case arrow IH𝕒 IH𝕓 =>
    simp
    constructor; apply IH𝕒; apply HwellBinds.right.left
    constructor; apply IH𝕓; apply HwellBinds.right.right
    simp [HwellBinds.left]
  case fragment => nomatch HwellBinds
  case rep => nomatch HwellBinds

lemma identity.ty.erase_typing_dyn : ∀ Γ e τ φ, typing Γ 𝟚 e τ φ → ‖τ‖𝜏 = τ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Γ e τ φ Hτ
  revert HEq𝕊
  apply @typing.rec
    (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => 𝟚 = 𝕊 → ‖τ‖𝜏 = τ)
    (fun Γ e τ φ (H : typing_reification Γ e τ φ) => true)
  <;> (try intros; assumption)
  <;> (try intros; contradiction)
  <;> (try intros; simp)
  <;> intros
  case fvar HwellBinds HEq𝕊 =>
    rw [← HEq𝕊] at HwellBinds
    apply identity.ty.erase_wbt_dyn
    apply HwellBinds
  case lam Hτe HwellBinds _ IHe HEq𝕊 =>
    rw [← HEq𝕊] at HwellBinds Hτe
    constructor; apply identity.ty.erase_wbt_dyn; apply HwellBinds
    constructor; apply IHe; apply HEq𝕊
    have ⟨_, HEqφ⟩ := typing.dyn_impl_pure _ _ _ _ Hτe
    simp [HEqφ]
  case app₁ IHf IHarg HEq𝕊 =>
    simp at IHf
    apply (IHf HEq𝕊).right.left
  case lets IHe HEq𝕊 =>
    apply IHe; apply HEq𝕊
