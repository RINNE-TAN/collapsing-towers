
import Mathlib.Tactic
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
  intros Γ Δ Φ v e τ𝕒 τ𝕓 φ Hτe HEqΓ Hτv
  revert Δ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ𝕓 φ (H : typing Γ 𝕊 e τ𝕓 φ) =>
        ∀ (Δ : TEnv), Γ = Δ ++ (τ𝕒, .stat) :: Φ →
          typing (Δ ++ Φ) 𝕊 (shiftr_at Φ.length (subst Φ.length v e)) τ𝕓 φ)
      (fun Γ e τ𝕓 φ (H : typing_reification Γ e τ𝕓 φ) =>
        ∀ (Δ : TEnv), Γ = Δ ++ (τ𝕒, .stat) :: Φ →
          typing_reification (Δ ++ Φ) (shiftr_at Φ.length (subst Φ.length v e)) τ𝕓 φ)
  case fvar =>
    intros _ 𝕊 x _ Hbinds Δ HEqΓ
    rw [HEqΓ] at Hbinds; simp
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      rw [if_neg (Nat.ne_of_lt Hx)]
      simp; rw [if_pos Hx]
      constructor
      have Hx : Φ.length <= x - 1 := by omega
      rw [← Nat.add_sub_of_le Hx, Nat.add_comm]
      apply binds_extendr
      rw [← Nat.sub_add_eq, Nat.add_comm]
      apply binds_shrinkr _ ((τ𝕒, .stat) :: Φ)
      rw [List.length_cons, Nat.sub_add_cancel]
      apply Hbinds; omega
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      rw [← Hx] at Hbinds; apply binds_shrink at Hbinds
      simp at Hbinds; rw [← Hbinds.left, ← Hbinds.right]
      rw [if_pos Hx]; rw [shiftr_id]
      apply weakening; apply Hτv
      apply closed_inc; apply typing_closed
      apply Hτv; omega; simp
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      rw [if_neg (Nat.ne_of_gt Hx)]
      simp; rw [if_neg (Nat.not_lt_of_gt Hx)]
      constructor
      apply binds_extend; apply binds_shrink
      omega; rw [List.append_cons] at Hbinds; apply Hbinds
  case lam₁ =>
    intros _ _ _ _ _ _ _ HwellBinds Hclose IH Δ HEqΓ
    rw [HEqΓ] at IH; rw [HEqΓ] at Hclose
    rw [subst_open₀_comm, shiftr_open₀_comm] at IH
    apply typing.lam₁
    simp; rw [← List.cons_append]
    simp at IH; apply IH; rfl
    apply HwellBinds
    cases Δ with
    | nil =>
      apply shiftr_closed_at_id; apply subst_closed_at_dec
      apply typing_closed; apply Hτv; apply Hclose
    | cons =>
      simp at *
      apply shiftr_closed_at; omega
      apply subst_closed_at; apply closed_inc
      apply typing_closed; apply Hτv; omega; apply Hclose
    simp; omega
    simp; omega
    apply typing_regular; apply Hτv
  case lift_lam =>
    intros _ _ _ _ _ _ _ IH Δ HEqΓ
    apply typing.lift_lam
    apply IH; apply HEqΓ
  case lam𝕔 =>
    intros _ _ _ _ _ _ HwellBinds Hclose IH Δ HEqΓ
    rw [HEqΓ] at IH; rw [HEqΓ] at Hclose
    rw [subst_open₀_comm, shiftr_open₀_comm] at IH
    apply typing.lam𝕔
    simp; rw [← List.cons_append]
    simp at IH; apply IH; rfl
    apply HwellBinds
    cases Δ with
    | nil =>
      apply shiftr_closed_at_id; apply subst_closed_at_dec
      apply typing_closed; apply Hτv; apply Hclose
    | cons =>
      simp at *
      apply shiftr_closed_at; omega
      apply subst_closed_at; apply closed_inc
      apply typing_closed; apply Hτv; omega; apply Hclose
    simp; omega
    simp; omega
    apply typing_regular; apply Hτv
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ IHf IHarg Δ HEqΓ
    apply typing.app₁
    apply IHf; apply HEqΓ
    apply IHarg; apply HEqΓ
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ IHf IHarg Δ HEqΓ
    apply typing.app₂
    apply IHf; apply HEqΓ
    apply IHarg; apply HEqΓ
  case plus₁ =>
    intros _ _ _ _ _ _ _ _ IHl IHr Δ HEqΓ
    apply typing.plus₁
    apply IHl; apply HEqΓ
    apply IHr; apply HEqΓ
  case plus₂ =>
    intros _ _ _ _ _ _ _ IHl IHr Δ HEqΓ
    apply typing.plus₂
    apply IHl; apply HEqΓ
    apply IHr; apply HEqΓ
  case lit₁ => intros; apply typing.lit₁
  case lift_lit =>
    intros _ _ _ _ IH Δ HEqΓ
    apply typing.lift_lit
    apply IH; apply HEqΓ
  case code₁ =>
    intros _ x _ Hbinds Δ HEqΓ
    rw [HEqΓ] at Hbinds; simp
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      rw [if_neg (Nat.ne_of_lt Hx)]
      simp; rw [if_pos Hx]
      apply typing.code₁
      have Hx : Φ.length <= x - 1 := by omega
      rw [← Nat.add_sub_of_le Hx, Nat.add_comm]
      apply binds_extendr
      rw [← Nat.sub_add_eq, Nat.add_comm]
      apply binds_shrinkr _ ((τ𝕒, .stat) :: Φ)
      rw [List.length_cons, Nat.sub_add_cancel]
      apply Hbinds; omega
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      rw [← Hx] at Hbinds; apply binds_shrink at Hbinds
      simp at Hbinds; simp
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      rw [if_neg (Nat.ne_of_gt Hx)]
      simp; rw [if_neg (Nat.not_lt_of_gt Hx)]
      apply typing.code₁
      apply binds_extend; apply binds_shrink
      omega; rw [List.append_cons] at Hbinds; apply Hbinds
  case code₂ =>
    intros _ _ _ _ IH Δ HEqΓ
    apply typing.code₂
    apply IH; apply HEqΓ
  case reflect =>
    intros _ _ _ _ IH Δ HEqΓ
    apply typing.reflect
    apply IH; apply HEqΓ
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe Δ HEqΓ
    rw [HEqΓ] at IHb; rw [HEqΓ] at IHe; rw [HEqΓ] at Hclose
    rw [subst_open₀_comm, shiftr_open₀_comm] at IHe
    simp at IHb; simp at IHe
    apply typing.lets
    apply IHb
    simp; rw [← List.cons_append]; apply IHe; rfl
    apply HwellBinds
    cases Δ with
    | nil =>
      simp at *; apply shiftr_closed_at_id
      apply subst_closed_at_dec
      apply typing_closed; apply Hτv
      apply Hclose
    | cons =>
      simp at *; apply shiftr_closed_at; omega
      apply subst_closed_at
      apply closed_inc; apply typing_closed; apply Hτv; omega
      apply Hclose
    simp; omega
    simp; omega
    apply typing_regular; apply Hτv
  case let𝕔 =>
    intros _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe Δ HEqΓ
    rw [HEqΓ] at IHb; rw [HEqΓ] at IHe; rw [HEqΓ] at Hclose
    rw [subst_open₀_comm, shiftr_open₀_comm] at IHe
    simp at IHb; simp at IHe
    apply typing.let𝕔
    apply IHb
    simp; rw [← List.cons_append]; apply IHe; rfl
    apply HwellBinds
    cases Δ with
    | nil =>
      simp at *; apply shiftr_closed_at_id
      apply subst_closed_at_dec
      apply typing_closed; apply Hτv
      apply Hclose
    | cons =>
      simp at *; apply shiftr_closed_at; omega
      apply subst_closed_at
      apply closed_inc; apply typing_closed; apply Hτv; omega
      apply Hclose
    simp; omega
    simp; omega
    apply typing_regular; apply Hτv
  case pure =>
    intros _ _ _ _ IH Δ HEqΓ
    apply typing_reification.pure
    apply IH; apply HEqΓ
  case reify =>
    intros _ _ _ _ IH Δ HEqΓ
    apply typing_reification.reify
    apply IH; apply HEqΓ
  apply Hτe

theorem preservation_subst :
    ∀ Γ v e τ𝕒 τ𝕓 φ,
      typing Γ .stat v τ𝕒 ∅ ->
      typing ((τ𝕒, .stat) :: Γ) .stat e τ𝕓 φ ->
      typing Γ .stat (subst Γ.length v e) τ𝕓 φ :=
  by
  intros Γ v e τ𝕒 τ𝕓 φ Hτv Hτe
  have H := preservation_subst_strengthened ((τ𝕒, .stat) :: Γ) [] Γ v e τ𝕒 τ𝕓 φ
  simp at H
  have H := H Hτe Hτv
  rw [shiftr_id] at H
  apply H
  apply subst_closed_at
  apply closed_inc; apply typing_closed; apply Hτv; omega
  rw [← List.length_cons]; apply typing_closed; apply Hτe

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
  case lets Hvalue =>
    cases Hτ
    case lets e v τ φ _ _ Hτv Hclose Hτe =>
    have Hpure : φ = ∅ := by
      apply typing_pure
      apply Hτv; apply Hvalue
    rw [Hpure] at Hτv; rw [Hpure, open_subst, union_pure_left]
    rw [← subst_intro]
    apply preservation_subst
    apply Hτv; apply Hτe; apply Hclose
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
