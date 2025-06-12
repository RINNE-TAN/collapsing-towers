
import Mathlib.Tactic
import CollapsingTowers.TwoLevelPCP.Typing
import CollapsingTowers.TwoLevelPCP.Shift

theorem preservation_subst_strengthened :
  ∀ Γ Δ Φ v e τ𝕒 τ𝕓 φ,
    typing Γ .stat e τ𝕓 φ →
    Γ = Δ ++ (τ𝕒, .stat) :: Φ →
    typing Φ .stat v τ𝕒 ∅ →
    typing (Δ ++ Φ) .stat (shiftr_at Φ.length (subst Φ.length v e)) τ𝕓 φ :=
  by
  intros Γ Δ Φ v e τ𝕒 τ𝕓 φ Hτe HEqΓ Hτv
  revert Δ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ𝕓 φ (H : typing Γ 𝕊 e τ𝕓 φ) =>
        ∀ Δ,
          Γ = Δ ++ (τ𝕒, .stat) :: Φ →
          typing (Δ ++ Φ) 𝕊 (shiftr_at Φ.length (subst Φ.length v e)) τ𝕓 φ)
      (fun Γ e τ𝕓 φ (H : typing_reification Γ e τ𝕓 φ) =>
        ∀ Δ,
          Γ = Δ ++ (τ𝕒, .stat) :: Φ →
          typing_reification (Δ ++ Φ) (shiftr_at Φ.length (subst Φ.length v e)) τ𝕓 φ)
  case fvar =>
    intros _ 𝕊 x _ Hbinds HwellBinds Δ HEqΓ
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
      apply Hbinds; omega; apply HwellBinds
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
      omega; rw [List.append_cons] at Hbinds; apply Hbinds; apply HwellBinds
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
  case code_fragment =>
    intros _ x _ Hbinds HwellBinds Δ HEqΓ
    rw [HEqΓ] at Hbinds; simp
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      rw [if_neg (Nat.ne_of_lt Hx)]
      simp; rw [if_pos Hx]
      apply typing.code_fragment
      have Hx : Φ.length <= x - 1 := by omega
      rw [← Nat.add_sub_of_le Hx, Nat.add_comm]
      apply binds_extendr
      rw [← Nat.sub_add_eq, Nat.add_comm]
      apply binds_shrinkr _ ((τ𝕒, .stat) :: Φ)
      rw [List.length_cons, Nat.sub_add_cancel]
      apply Hbinds; omega; apply HwellBinds
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      rw [← Hx] at Hbinds; apply binds_shrink at Hbinds
      simp at Hbinds; simp
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      rw [if_neg (Nat.ne_of_gt Hx)]
      simp; rw [if_neg (Nat.not_lt_of_gt Hx)]
      apply typing.code_fragment
      apply binds_extend; apply binds_shrink
      omega; rw [List.append_cons] at Hbinds; apply Hbinds; apply HwellBinds
  case code_rep =>
    intros _ _ _ _ IH Δ HEqΓ
    apply typing.code_rep
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
    intros _ _ _ _ _ IH Δ HEqΓ
    apply typing_reification.reify
    apply IH; apply HEqΓ
  apply Hτe

theorem preservation_subst :
  ∀ Γ v e τ𝕒 τ𝕓 φ,
    typing Γ .stat v τ𝕒 ∅ →
    typing ((τ𝕒, .stat) :: Γ) .stat e τ𝕓 φ →
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

theorem preservation_maping_strengthened :
  ∀ Δ Φ v e τ𝕒 τ𝕓 τ𝕔 𝕊𝕒 φ,
    typing (Δ ++ (τ𝕔, .stat) :: Φ) .stat e τ𝕓 φ →
    typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) .stat v τ𝕔 ∅ →
    typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) .stat (subst Φ.length v e) τ𝕓 φ :=
  by
  intros Δ Φ v e τ𝕒 τ𝕓 τ𝕔 𝕊𝕒 φ
  generalize HEqΓ : Δ ++ (τ𝕔, .stat) :: Φ = Γ
  intros Hτe Hτv
  revert Δ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ𝕓 φ (H : typing Γ 𝕊 e τ𝕓 φ) =>
        ∀ Δ,
          Δ ++ (τ𝕔, .stat) :: Φ = Γ →
          typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) .stat v τ𝕔 ∅ →
          typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) 𝕊 (subst Φ.length v e) τ𝕓 φ)
      (fun Γ e τ𝕓 φ (H : typing_reification Γ e τ𝕓 φ) =>
        ∀ Δ,
          Δ ++ (τ𝕔, .stat) :: Φ = Γ →
          typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) .stat v τ𝕔 ∅ →
          typing_reification (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) (subst Φ.length v e) τ𝕓 φ)
  case fvar =>
    intros _ 𝕊 x _ Hbinds HwellBinds Δ HEqΓ Hτv
    rw [← HEqΓ] at Hbinds
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      simp; rw [if_neg (Nat.ne_of_lt Hx)]
      apply typing.fvar
      have Hx : ((τ𝕒, 𝕊𝕒) :: Φ).length <= x := by simp; omega
      rw [← Nat.add_sub_of_le Hx, Nat.add_comm]
      apply binds_extendr
      apply binds_shrinkr _ ((τ𝕔, .stat) :: Φ)
      rw [List.length_cons, List.length_cons, Nat.sub_add_cancel]
      apply Hbinds; omega; apply HwellBinds
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      rw [← Hx] at Hbinds
      apply binds_shrink at Hbinds
      simp at Hbinds; rw [← Hbinds.left, ← Hbinds.right]
      simp; rw [if_pos Hx]; apply Hτv; simp
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      simp; rw [if_neg (Nat.ne_of_gt Hx)]
      rw [List.append_cons]
      rw [List.append_cons] at Hbinds
      apply typing.fvar
      apply binds_extend; apply binds_shrink
      omega; apply Hbinds; apply HwellBinds
  case lam₁ =>
    intros _ _ _ _ _ _ _ HwellBinds Hclose IH Δ HEqΓ Hτv
    rw [← HEqΓ, List.length_append, List.length_cons] at Hclose
    rw [← HEqΓ, subst_open₀_comm, List.length_append, List.length_cons] at IH
    apply typing.lam₁
    rw [← List.cons_append, List.length_append, List.length_cons]
    apply IH; rfl
    apply weakening1; apply Hτv; apply HwellBinds
    apply subst_closed_at
    apply typing_closed; apply Hτv
    rw [List.length_append, List.length_cons]; apply Hclose
    simp; omega
    apply typing_regular; apply Hτv
  case lift_lam =>
    intros _ _ _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.lift_lam
    apply IH; apply HEqΓ; apply Hτv
  case lam𝕔 =>
    intros _ _ _ _ _ _ HwellBinds Hclose IH Δ HEqΓ Hτv
    rw [← HEqΓ, List.length_append, List.length_cons] at Hclose
    rw [← HEqΓ, subst_open₀_comm, List.length_append, List.length_cons] at IH
    apply typing.lam𝕔
    rw [← List.cons_append, List.length_append, List.length_cons]
    apply IH; rfl
    apply weakening1; apply Hτv; apply HwellBinds
    apply subst_closed_at
    apply typing_closed; apply Hτv
    rw [List.length_append, List.length_cons]; apply Hclose
    simp; omega; apply typing_regular; apply Hτv
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ IHf IHarg Δ HEqΓ Hτv
    apply typing.app₁
    apply IHf; apply HEqΓ; apply Hτv
    apply IHarg; apply HEqΓ; apply Hτv
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ IHf IHarg Δ HEqΓ Hτv
    apply typing.app₂
    apply IHf; apply HEqΓ; apply Hτv
    apply IHarg; apply HEqΓ; apply Hτv
  case plus₁ =>
    intros _ _ _ _ _ _ _ _ IHl IHr Δ HEqΓ Hτv
    apply typing.plus₁
    apply IHl; apply HEqΓ; apply Hτv
    apply IHr; apply HEqΓ; apply Hτv
  case plus₂ =>
    intros _ _ _ _ _ _ _ IHl IHr Δ HEqΓ Hτv
    apply typing.plus₂
    apply IHl; apply HEqΓ; apply Hτv
    apply IHr; apply HEqΓ; apply Hτv
  case lit₁ => intros; apply typing.lit₁
  case lift_lit =>
    intros _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.lift_lit
    apply IH; apply HEqΓ; apply Hτv
  case code_fragment =>
    intros _ x _ Hbinds HwellBinds Δ HEqΓ Hτv
    rw [← HEqΓ] at Hbinds
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      simp; rw [if_neg (Nat.ne_of_lt Hx)]
      apply typing.code_fragment
      have Hx : ((τ𝕒, 𝕊𝕒) :: Φ).length <= x := by simp; omega
      rw [← Nat.add_sub_of_le Hx, Nat.add_comm]
      apply binds_extendr
      apply binds_shrinkr _ ((τ𝕔, .stat) :: Φ)
      rw [List.length_cons, List.length_cons, Nat.sub_add_cancel]
      apply Hbinds; omega; apply HwellBinds
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      rw [← Hx] at Hbinds
      apply binds_shrink at Hbinds
      simp at Hbinds; simp
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      simp; rw [if_neg (Nat.ne_of_gt Hx)]
      rw [List.append_cons]
      rw [List.append_cons] at Hbinds
      apply typing.code_fragment
      apply binds_extend; apply binds_shrink
      omega; apply Hbinds; apply HwellBinds
  case code_rep =>
    intros _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.code_rep
    apply IH; apply HEqΓ; apply Hτv
  case reflect =>
    intros _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.reflect
    apply IH; apply HEqΓ; apply Hτv
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe Δ HEqΓ Hτv
    rw [← HEqΓ, List.length_append, List.length_cons] at Hclose
    rw [← HEqΓ] at IHb
    rw [← HEqΓ, subst_open₀_comm, List.length_append, List.length_cons] at IHe
    apply typing.lets
    apply IHb; rfl; apply Hτv
    rw [← List.cons_append, List.length_append, List.length_cons]
    apply IHe; rfl
    apply weakening1; apply Hτv; apply HwellBinds
    apply subst_closed_at
    apply typing_closed; apply Hτv
    rw [List.length_append, List.length_cons]; apply Hclose
    simp; omega
    apply typing_regular; apply Hτv
  case let𝕔 =>
    intros _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe Δ HEqΓ Hτv
    rw [← HEqΓ, List.length_append, List.length_cons] at Hclose
    rw [← HEqΓ] at IHb
    rw [← HEqΓ, subst_open₀_comm, List.length_append, List.length_cons] at IHe
    apply typing.let𝕔
    apply IHb; rfl; apply Hτv
    rw [← List.cons_append, List.length_append, List.length_cons]
    apply IHe; rfl
    apply weakening1; apply Hτv; apply HwellBinds
    apply subst_closed_at
    apply typing_closed; apply Hτv
    rw [List.length_append, List.length_cons]; apply Hclose
    simp; omega
    apply typing_regular; apply Hτv
  case pure =>
    intros _ _ _ _ IH Δ HEqΓ Hτv
    apply typing_reification.pure
    apply IH; apply HEqΓ; apply Hτv
  case reify =>
    intros _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing_reification.reify
    apply IH; apply HEqΓ; apply Hτv
  apply Hτe

theorem preservation_maping :
  ∀ Γ v e τ𝕒 τ𝕓 τ𝕔 𝕊𝕒 φ,
    typing ((τ𝕔, .stat) :: Γ) .stat e τ𝕓 φ →
    typing ((τ𝕒, 𝕊𝕒) :: Γ) .stat v τ𝕔 ∅ →
    typing ((τ𝕒, 𝕊𝕒) :: Γ) .stat (subst Γ.length v e) τ𝕓 φ := by
  intros Γ v e τ𝕒 τ𝕓 τ𝕔 𝕊𝕒 φ
  rw [← List.nil_append ((τ𝕔, .stat) :: Γ), ← List.nil_append ((τ𝕒, 𝕊𝕒) :: Γ)]
  apply preservation_maping_strengthened

theorem preservation_head𝕄 :
  ∀ Γ e₀ e₁ τ φ,
    head𝕄 e₀ e₁ →
    lc e₀ →
    typing Γ .stat e₀ τ φ →
    typing Γ .stat e₁ τ φ :=
  by
  intros Γ e₀ e₁ τ φ Hhead Hlc Hτ
  cases Hhead
  case lets Hvalue =>
    cases Hτ
    case lets e v τ φ _ _ Hτv Hclose
      Hτe =>
      have Hpure : φ = ∅ := by
        apply typing_value_pure
        apply Hτv; apply Hvalue
      rw [Hpure] at Hτv; rw [Hpure, open_subst, union_pure_left]
      rw [← subst_intro]; apply preservation_subst
      apply Hτv; apply Hτe; apply Hclose
  case app₁ Hvalue =>
    cases Hτ
    case app₁ φ Hτv Hτf =>
      cases Hτf
      case lam₁ Hclose _
        Hτe =>
        have Hpure : φ = ∅ := by
          apply typing_value_pure
          apply Hτv; apply Hvalue
        rw [Hpure] at Hτv; rw [Hpure, open_subst, union_pure_right, union_pure_right]
        rw [← subst_intro]; apply preservation_subst
        apply Hτv; apply Hτe; apply Hclose
  case app₂ =>
    cases Hτ
    case app₂ Hτ₀ Hτ₁ =>
      cases Hτ₀
      case code_fragment HwellBinds₀ Hbinds₀ =>
        cases Hτ₁
        case code_fragment HwellBinds₁ Hbinds₁ =>
          apply typing.reflect
          rw [← union_pure_right ∅, ← union_pure_right (∅ ∪ ∅)]
          apply typing.app₁
          apply typing.fvar; apply Hbinds₀; apply HwellBinds₀
          apply typing.fvar; apply Hbinds₁; apply HwellBinds₁
  case plus₁ =>
    cases Hτ
    case plus₁ Hl Hr =>
      cases Hl; cases Hr; apply typing.lit₁
  case plus₂ =>
    cases Hτ
    case plus₂ Hτ₀ Hτ₁ =>
      cases Hτ₀
      case code_fragment HwellBinds₀ Hbinds₀ =>
        cases Hτ₁
        case code_fragment HwellBinds₁ Hbinds₁ =>
          apply typing.reflect
          rw [← union_pure_right ∅, ← union_pure_right (∅ ∪ ∅)]
          apply typing.plus₁
          apply typing.fvar; apply Hbinds₀; apply HwellBinds₀
          apply typing.fvar; apply Hbinds₁; apply HwellBinds₁
  case lift_lit =>
    cases Hτ
    case lift_lit Hτ =>
      apply typing.reflect
      apply typing.lit₁
    case lift_lam => contradiction
  case lift_lam e =>
    cases Hτ
    case lift_lit => contradiction
    case lift_lam Hτ =>
      cases Hτ
      case lam₁ Hclose HwellBinds Hτe =>
        rw [← map𝕔₀_intro Γ.length]
        apply typing.lam𝕔
        simp; rw [open_close_id]
        apply typing_reification.reify
        apply preservation_maping
        apply Hτe
        apply typing.code_fragment; simp
        apply HwellBinds
        apply subst_closedb_at; simp; apply open_closedb'; apply Hlc
        apply HwellBinds
        apply close_closed; apply subst_closed_at; simp; apply open_closed; apply Hclose
        apply Hclose
  case lam𝕔 e =>
    cases Hτ
    case lam𝕔 HwellBinds Hτ Hclose =>
      apply typing.reflect
      apply typing.lam₁
      cases Hτ with
      | pure _ _ _ Hτ =>
        simp at *
        generalize Eqe : opening 0 (.fvar (List.length Γ)) e = E
        rw [Eqe] at Hτ
        cases Hτ with
        | code_rep _ _ _ Hτ => apply Hτ
      | reify _ _ _ _ Hτ =>
        simp at *
        generalize Eqe : opening 0 (.fvar (List.length Γ)) e = E
        rw [Eqe] at Hτ
        cases Hτ with
        | code_fragment _ _ _ Hbinds HwellBinds =>
          apply typing.fvar
          apply Hbinds; apply HwellBinds
      apply HwellBinds
      apply Hclose
  case let𝕔 e =>
    cases Hτ
    case let𝕔 HwellBinds Hτb Hτe Hclose =>
      apply typing.code_rep
      rw [← union_pure_right ∅]
      apply typing.lets
      apply Hτb
      cases Hτe with
      | pure _ _ _ Hτ =>
        simp at *
        generalize Eqe : opening 0 (.fvar (List.length Γ)) e = E
        rw [Eqe] at Hτ
        cases Hτ with
        | code_rep _ _ _ Hτ => apply Hτ
      | reify _ _ _ _ Hτ =>
        simp at *
        generalize Eqe : opening 0 (.fvar (List.length Γ)) e = E
        rw [Eqe] at Hτ
        cases Hτ with
        | code_fragment _ _ _ Hbinds HwellBinds =>
          apply typing.fvar
          apply Hbinds; apply HwellBinds
      apply HwellBinds
      apply Hclose

theorem preservationℝ :
  ∀ Γ R e₀ e₁ τ φ,
    ctxℝ Γ.length R →
    lc e₀ →
    (∀ τ𝕒 τ𝕓 φ,
      typing (τ𝕒 :: Γ) .stat e₀ τ𝕓 φ →
      typing (τ𝕒 :: Γ) .stat e₁ τ𝕓 φ
    ) →
    typing Γ .stat (R e₀) τ φ →
    typing Γ .stat (R e₁) τ φ :=
  by
  intros Γ R e₀ e₁ τ φ HR Hlc IH Hτ
  cases HR
  case lam𝕔 =>
    cases Hτ
    case lam𝕔 HwellBinds IHe Hclose =>
      rw [open_close_id₀] at IHe
      . cases IHe with
        | pure _ _ _ IHe₀ =>
          have IHe₁ := IH _ _ _ IHe₀
          apply typing.lam𝕔
          apply typing_reification.pure
          rw [open_close_id₀]
          apply IHe₁; apply typing_regular; apply IHe₁
          apply HwellBinds
          apply close_closed; rw [← List.length_cons]
          apply typing_closed; apply IHe₁
        | reify _ _ _ _ IHe₀ =>
          have IHe₁ := IH _ _ _ IHe₀
          apply typing.lam𝕔
          apply typing_reification.reify
          rw [open_close_id₀]
          apply IHe₁; apply typing_regular; apply IHe₁
          apply HwellBinds
          apply close_closed; rw [← List.length_cons]
          apply typing_closed; apply IHe₁
      apply Hlc
  case let𝕔 =>
    cases Hτ
    case let𝕔 HwellBinds IHb IHe Hclose =>
      rw [open_close_id₀] at IHe
      . cases IHe with
        | pure _ _ _ IHe₀ =>
          have IHe₁ := IH _ _ _ IHe₀
          apply typing.let𝕔; apply IHb
          apply typing_reification.pure
          rw [open_close_id₀]
          apply IHe₁; apply typing_regular; apply IHe₁
          apply HwellBinds
          apply close_closed; rw [← List.length_cons]
          apply typing_closed; apply IHe₁
        | reify _ _ _ _ IHe₀ =>
          have IHe₁ := IH _ _ _ IHe₀
          apply typing.let𝕔; apply IHb
          apply typing_reification.reify
          rw [open_close_id₀]
          apply IHe₁; apply typing_regular; apply IHe₁
          apply HwellBinds
          apply close_closed; rw [← List.length_cons]
          apply typing_closed; apply IHe₁
      apply Hlc

theorem preservation𝔹 :
  ∀ Γ B e₀ e₁ τ φ,
    ctx𝔹 B →
    (∀ τ φ,
      typing Γ .stat e₀ τ φ →
      typing Γ .stat e₁ τ φ
    ) →
    typing Γ .stat (B e₀) τ φ →
    typing Γ .stat (B e₁) τ φ :=
  by
  intros Γ B e₀ e₁ τ φ HB IH Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ IHarg IHf =>
      apply typing.app₁
      apply IH; apply IHf; apply IHarg
  case appr₁ =>
    cases Hτ
    case app₁ IHarg IHf =>
      apply typing.app₁
      apply IHf; apply IH; apply IHarg
  case appl₂ =>
    cases Hτ
    case app₂ IHf IHarg =>
      apply typing.app₂
      apply IH; apply IHf; apply IHarg
  case appr₂ =>
    cases Hτ
    case app₂ IHf IHarg =>
      apply typing.app₂
      apply IHf; apply IH; apply IHarg
  case plusl₁ =>
    cases Hτ
    case plus₁ IHl IHr =>
      apply typing.plus₁
      apply IH; apply IHl; apply IHr
  case plusr₁ =>
    cases Hτ
    case plus₁ IHl IHr =>
      apply typing.plus₁
      apply IHl; apply IH; apply IHr
  case plusl₂ =>
    cases Hτ
    case plus₂ IHl IHr =>
      apply typing.plus₂
      apply IH; apply IHl; apply IHr
  case plusr₂ =>
    cases Hτ
    case plus₂ IHl IHr =>
      apply typing.plus₂
      apply IHl; apply IH; apply IHr
  case lift =>
    cases Hτ
    case lift_lit IHn =>
      apply typing.lift_lit
      apply IH; apply IHn
    case lift_lam IHe =>
      apply typing.lift_lam
      apply IH; apply IHe
  case lets =>
    cases Hτ
    case lets HwellBinds IHb Hclose IHe =>
      apply typing.lets
      apply IH; apply IHb; apply IHe
      apply HwellBinds; apply Hclose

theorem preservation𝕄 :
  ∀ Γ M e₀ e₁ τ φ,
    ctx𝕄 Γ.length M →
    lc e₀ →
    head𝕄 e₀ e₁ →
    typing Γ .stat (M e₀) τ φ →
    typing Γ .stat (M e₁) τ φ :=
  by
  intros Γ M e₀ e₁ τ φ HM Hlc Hhead𝕄 Hτ
  generalize HEqlvl : Γ.length = lvl
  rw [HEqlvl] at HM
  induction HM generalizing τ φ Γ with
  | hole =>
    apply preservation_head𝕄
    apply Hhead𝕄; apply Hlc; apply Hτ
  | cons𝔹 _ _ HB _ IHM =>
    simp; apply preservation𝔹
    apply HB; intros _ _ IHτ
    apply IHM; apply IHτ; apply HEqlvl; apply Hτ
  | consℝ _ _ HR HM IHM =>
    simp; apply preservationℝ
    rw [HEqlvl]; apply HR
    apply lc_ctx𝕄
    apply HM; apply Hlc; intros _ _ _ IHτ
    apply IHM; apply IHτ; simp; omega; apply Hτ

theorem pure𝔹 :
  ∀ Γ B e τ φ,
    ctx𝔹 B →
    φ = ∅ →
    typing Γ Stage.stat (B e) τ φ →
    ∃ τ, typing Γ Stage.stat e τ ∅  :=
  by
  intros Γ B e τ φ HB HEqφ Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ φ₀ φ₁ φ₂ IHarg IHf =>
      cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> try contradiction
      constructor; apply IHf
  case appr₁ =>
    cases Hτ
    case app₁ φ₀ φ₁ φ₂ IHarg IHf =>
      cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> try contradiction
      constructor; apply IHarg
  case appl₂ =>
    cases Hτ
    case app₂ IHf IHarg =>
      contradiction
  case appr₂ =>
    cases Hτ
    case app₂ IHf IHarg =>
      contradiction
  case plusl₁ =>
    cases Hτ
    case plus₁ φ₀ φ₁ IHl IHr =>
      cases φ₀ <;> cases φ₁ <;> try contradiction
      constructor; apply IHl
  case plusr₁ =>
    cases Hτ
    case plus₁ φ₀ φ₁ IHl IHr =>
      cases φ₀ <;> cases φ₁ <;> try contradiction
      constructor; apply IHr
  case plusl₂ =>
    cases Hτ
    case plus₂ IHl IHr =>
      contradiction
  case plusr₂ =>
    cases Hτ
    case plus₂ IHl IHr =>
      contradiction
  case lift =>
    cases Hτ
    case lift_lit IHn =>
      contradiction
    case lift_lam IHe =>
      contradiction
  case lets =>
    cases Hτ
    case lets φ₀ φ₁ HwellBinds IHb Hclose IHe =>
      cases φ₀ <;> cases φ₁ <;> try contradiction
      constructor; apply IHb

theorem decompose𝔼 :
  ∀ Γ E e τ φ,
    ctx𝔼 E →
    typing Γ .stat (E e) τ φ →
    ∃ τ𝕖 φ𝕖 φ𝔼,
      φ = φ𝕖 ∪ φ𝔼 ∧
      typing Γ .stat e τ𝕖 φ𝕖 ∧
      ∀ e φ Δ,
        typing (Δ ++ Γ) .stat e τ𝕖 φ →
        typing (Δ ++ Γ) .stat (E e) τ (φ ∪ φ𝔼) :=
  by
  intros Γ E e τ φ HE Hτ
  induction HE generalizing φ τ with
  | hole =>
    exists τ, φ, ∅
    constructor; cases φ <;> rfl
    constructor; apply Hτ
    intros e φ Δ Hτ; cases φ <;> apply Hτ
  | cons𝔹 _ _ HB _ IH =>
    cases HB
    case appl₁ =>
      cases Hτ
      case app₁ φ₀ φ₁ φ₂ Harg HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, (φ₀ ∪ φ𝔼 ∪ φ₂)
        constructor
        . rw [HEqφ]
          cases φ₀ <;> cases φ₂ <;>
          cases φ𝕖 <;> cases φ𝔼 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ (φ₀ ∪ φ𝔼 ∪ φ₂)) = φ₀ ∪ (φ ∪ φ𝔼) ∪ φ₂ :=
            by
            cases φ₀ <;> cases φ₂ <;>
            cases φ <;> cases φ𝔼 <;> simp
          rw [HEqφ]
          apply typing.app₁
          apply IH; apply He
          apply weakening; apply Harg
    case appr₁ =>
      cases Hτ
      case app₁ φ₀ φ₁ φ₂ HX Hf =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, (φ₀ ∪ φ₁ ∪ φ𝔼)
        constructor
        . rw [HEqφ]
          cases φ₀ <;> cases φ₁ <;>
          cases φ𝕖 <;> cases φ𝔼 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ (φ₀ ∪ φ₁ ∪ φ𝔼)) = φ₀ ∪ φ₁ ∪ (φ ∪ φ𝔼) :=
            by
            cases φ₀ <;> cases φ₁ <;>
            cases φ <;> cases φ𝔼 <;> simp
          rw [HEqφ]
          apply typing.app₁
          apply weakening; apply Hf
          apply IH; apply He
    case appl₂ =>
      cases Hτ
      case app₂ φ₀ φ₁ HX Harg =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.app₂
          apply IH; apply He
          apply weakening; apply Harg
    case appr₂ =>
      cases Hτ
      case app₂ φ₀ φ₁ Hf HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.app₂
          apply weakening; apply Hf
          apply IH; apply He
    case plusl₁ =>
      cases Hτ
      case plus₁ φ₀ φ₁ HX Hr =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, (φ₁ ∪ φ𝔼)
        constructor
        . rw [HEqφ]
          cases φ₁ <;> cases φ𝕖 <;> cases φ𝔼 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ (φ₁ ∪ φ𝔼)) = ((φ ∪ φ𝔼) ∪ φ₁) :=
            by cases φ₁ <;> cases φ <;> cases φ𝔼 <;> simp
          rw [HEqφ]
          apply typing.plus₁
          apply IH; apply He
          apply weakening; apply Hr
    case plusr₁ =>
      cases Hτ
      case plus₁ φ₀ φ₁ Hl HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, (φ₀ ∪ φ𝔼)
        constructor
        . rw [HEqφ]
          cases φ₀ <;> cases φ𝕖 <;> cases φ𝔼 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ (φ₀ ∪ φ𝔼)) = (φ₀ ∪ (φ ∪ φ𝔼)) :=
            by cases φ₀ <;> cases φ <;> cases φ𝔼 <;> simp
          rw [HEqφ]
          apply typing.plus₁
          apply weakening; apply Hl
          apply IH; apply He
    case plusl₂ =>
      cases Hτ
      case plus₂ φ₀ φ₁ HX Hr =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.plus₂
          apply IH; apply He
          apply weakening; apply Hr
    case plusr₂ =>
      cases Hτ
      case plus₂ φ₀ φ₁ Hl HX =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, .reify
        constructor
        . cases φ𝕖 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ .reify) = .reify :=
            by cases φ <;> simp
          rw [HEqφ]
          apply typing.plus₂
          apply weakening; apply Hl
          apply IH; apply He
    case lift => admit
    case lets =>
      cases Hτ
      case lets φ₀ φ₁ HwellBinds HX Hclose Hbody =>
        have ⟨τ𝕖, φ𝕖, φ𝔼, HEqφ, He, IH⟩ := IH _ _ HX
        exists τ𝕖, φ𝕖, (φ₁ ∪ φ𝔼)
        constructor
        . rw [HEqφ]
          cases φ₁ <;> cases φ𝕖 <;> cases φ𝔼 <;> simp
        . constructor; apply He
          intros e φ Δ He
          have HEqφ : (φ ∪ (φ₁ ∪ φ𝔼)) = ((φ ∪ φ𝔼) ∪ φ₁) :=
            by cases φ₁ <;> cases φ <;> cases φ𝔼 <;> simp
          rw [HEqφ]
          apply typing.lets
          apply IH; apply He
          all_goals admit

theorem preservation_reflect :
  ∀ Γ E e τ φ,
    ctx𝔼 E →
    typing_reification Γ (E (.reflect e)) τ φ →
    typing_reification Γ (.let𝕔 e (E (.code (.bvar 0)))) τ ∅ :=
  by
  intros Γ E e τ φ HE Hτ
  cases Hτ
  case pure Hτ =>
    exfalso
    induction HE generalizing τ with
    | hole => nomatch Hτ
    | cons𝔹 _ _ HB _ IH =>
      have ⟨_, Hτ⟩ := pure𝔹 _ _ _ _ _ HB (by rfl) Hτ
      apply IH; apply Hτ
  case reify τ Hτ =>
    have ⟨τ𝕖, φ₀, φ₁, HEqφ, Hτr, HτE⟩ := decompose𝔼 _ _ _ _ _ HE Hτ
    cases Hτr with
    | reflect _ _ _ Hτe =>
      have ⟨HwellBinds, _⟩ := typing_dyn_pure _ _ _ _ Hτe
      apply typing_reification.pure
      apply typing.let𝕔; apply Hτe
      apply typing_reification.reify
      rw [open_ctx𝔼_map _ _ _ HE, ← List.singleton_append]
      apply HτE; apply typing.code_fragment; simp
      apply HwellBinds
      apply HwellBinds
      apply closed_at𝔼; apply HE
      apply typing_closed; apply Hτ; simp

theorem preservationℚ :
  ∀ Γ lvl Q E e τ φ,
    Γ.length = lvl →
    ctxℚ lvl Q →
    ctx𝔼 E →
    lc e →
    typing Γ .stat (Q (E (.reflect e))) τ φ →
    typing Γ .stat (Q (.let𝕔 e (E (.code (.bvar 0))))) τ φ :=
  by
  intros Γ lvl Q E e τ φ HEqlvl HQ HE Hlc Hτ
  induction HQ generalizing τ φ Γ with
  | holeℝ _ HR =>
    cases HR
    case lam𝕔 =>
      rw [← HEqlvl] at Hτ; rw [← HEqlvl]
      cases Hτ
      case lam𝕔 HwellBinds IHe Hclose =>
        rw [open_close_id₀] at IHe
        apply typing.lam𝕔; rw [open_close_id₀]
        apply preservation_reflect; apply HE; apply IHe
        constructor; apply Hlc
        apply lc_ctx𝔼; apply HE; simp
        apply HwellBinds
        apply close_closed; constructor
        apply closed_at_decompose𝔼 _ (.reflect e) _ HE
        rw [← List.length_cons]; apply typing_reification_closed; apply IHe
        apply closed_at𝔼; apply HE
        rw [← List.length_cons]; apply typing_reification_closed; apply IHe; simp
        apply lc_ctx𝔼; apply HE; apply Hlc
    case let𝕔 =>
      rw [← HEqlvl] at Hτ; rw [← HEqlvl]
      cases Hτ
      case let𝕔 HwellBinds IHb IHe Hclose =>
        rw [open_close_id₀] at IHe
        apply typing.let𝕔; apply IHb; rw [open_close_id₀]
        apply preservation_reflect; apply HE; apply IHe
        constructor; apply Hlc
        apply lc_ctx𝔼; apply HE; simp
        apply HwellBinds
        apply close_closed; constructor
        apply closed_at_decompose𝔼 _ (.reflect e) _ HE
        rw [← List.length_cons]; apply typing_reification_closed; apply IHe
        apply closed_at𝔼; apply HE
        rw [← List.length_cons]; apply typing_reification_closed; apply IHe; simp
        apply lc_ctx𝔼; apply HE; apply Hlc
  | cons𝔹 _ _ HB _ IHQ =>
    simp; apply preservation𝔹
    apply HB; intros _ _ IHτ
    apply IHQ; apply HEqlvl; apply IHτ; apply Hτ
  | consℝ R Q HR HQ IHQ =>
    simp; apply preservationℝ _ _ (Q (E (.reflect e)))
    rw [HEqlvl]; apply HR
    apply lc_ctxℚ; apply HQ
    apply lc_ctx𝔼; apply HE
    apply Hlc; intros _ _ _ IHτ
    apply IHQ; simp; omega; apply IHτ; apply Hτ

theorem preservation_strengthened :
  ∀ Γ e₀ e₁ τ φ₀,
    step_lvl Γ.length e₀ e₁ →
    typing_reification Γ e₀ τ φ₀ →
    ∃ φ₁, typing_reification Γ e₁ τ φ₁ ∧ φ₁ <= φ₀ :=
  by
  intro Γ e₀ e₁ τ φ₀
  intro Hstep Hτ; cases Hstep
  case step𝕄 HM Hlc Hhead𝕄 =>
    exists φ₀; constructor
    . cases Hτ
      all_goals
        next Hτ =>
        constructor
        apply preservation𝕄
        apply HM; apply Hlc; apply Hhead𝕄; apply Hτ
    . rfl
  case reflect P E e HP HE Hlc =>
    generalize HEqlvl : Γ.length = lvl
    rw [HEqlvl] at HP
    cases HP
    case hole =>
      exists ∅; constructor
      . apply preservation_reflect
        apply HE; apply Hτ
      . rfl
    case consℚ HQ =>
      exists φ₀; constructor
      . cases Hτ
        all_goals
          next Hτ =>
          constructor
          apply preservationℚ
          apply HEqlvl; apply HQ; apply HE; apply Hlc; apply Hτ
      . rfl
