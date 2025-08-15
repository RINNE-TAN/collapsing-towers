import CollapsingTowers.TwoLevelRec.SyntacticTyping.Defs

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
  | (τ, _) :: Γ => (‖τ‖𝜏, 𝟚) :: erase Γ

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

lemma env.erase.binds : ∀ x τ 𝕊 Γ, binds x (τ, 𝕊) Γ → binds x (‖τ‖𝜏, 𝟚) ‖Γ‖𝛾 :=
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

lemma erasable.fragment : ∀ τ₀ τ₁, ‖τ₀‖𝜏 ≠ .fragment τ₁ :=
  by
  intros τ₀ τ₁
  induction τ₀ <;> simp
  all_goals next IH => apply IH

lemma erasable.rep : ∀ τ₀ τ₁, ‖τ₀‖𝜏 ≠ .rep τ₁ :=
  by
  intros τ₀ τ₁
  induction τ₀ <;> simp
  all_goals next IH => apply IH

lemma wbt_dyn_iff_erase_identity : ∀ τ, wbt 𝟚 τ ↔ ‖τ‖𝜏 = τ :=
  by
  intros τ
  induction τ
  case nat => simp
  case arrow IH𝕒 IH𝕓 =>
    simp [IH𝕒, IH𝕓]
    constructor
    . intros H; simp [H]
    . intros H; simp [H]
  case fragment => simp; apply erasable.fragment
  case rep => simp; apply erasable.rep
