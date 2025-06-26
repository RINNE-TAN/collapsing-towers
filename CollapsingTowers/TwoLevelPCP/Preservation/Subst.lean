
import Mathlib.Tactic
import CollapsingTowers.TwoLevelPCP.Typing
import CollapsingTowers.TwoLevelPCP.Shift
theorem preservation_subst_strengthened :
  ∀ Γ Δ Φ σ v e τ𝕒 τ𝕓 φ,
    typing Γ σ .stat e τ𝕓 φ →
    Γ = Δ ++ (τ𝕒, .stat) :: Φ →
    typing Φ σ .stat v τ𝕒 ∅ →
    typing (Δ ++ Φ) σ .stat (shiftr_at Φ.length (subst Φ.length v e)) τ𝕓 φ :=
  by
  intros Γ Δ Φ σ v e τ𝕒 τ𝕓 φ Hτe HEqΓ
  revert Δ
  apply
    @typing.rec
      (fun Γ σ 𝕊 e τ𝕓 φ (H : typing Γ σ 𝕊 e τ𝕓 φ) =>
        ∀ Δ,
          Γ = Δ ++ (τ𝕒, .stat) :: Φ →
          typing Φ σ .stat v τ𝕒 ∅ →
          typing (Δ ++ Φ) σ 𝕊 (shiftr_at Φ.length (subst Φ.length v e)) τ𝕓 φ)
      (fun Γ σ e τ𝕓 φ (H : typing_reification Γ σ e τ𝕓 φ) =>
        ∀ Δ,
          Γ = Δ ++ (τ𝕒, .stat) :: Φ →
          typing Φ σ .stat v τ𝕒 ∅ →
          typing_reification (Δ ++ Φ) σ (shiftr_at Φ.length (subst Φ.length v e)) τ𝕓 φ)
  case fvar =>
    intros _ _ 𝕊 x _ Hbinds HwellBinds Δ HEqΓ Hτv
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
    intros _ _ _ _ _ _ _ _ HwellBinds Hclose IH Δ HEqΓ Hτv
    rw [HEqΓ] at IH; rw [HEqΓ] at Hclose
    rw [subst_open₀_comm, shiftr_open₀_comm] at IH
    apply typing.lam₁
    simp; rw [← List.cons_append]
    simp at IH; apply IH; rfl
    apply Hτv; apply HwellBinds
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
    intros _ _ _ _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.lift_lam
    apply IH; apply HEqΓ; apply Hτv
  case lam𝕔 =>
    intros _ _ _ _ _ _ _ HwellBinds Hclose IH Δ HEqΓ Hτv
    rw [HEqΓ] at IH; rw [HEqΓ] at Hclose
    rw [subst_open₀_comm, shiftr_open₀_comm] at IH
    apply typing.lam𝕔
    simp; rw [← List.cons_append]
    simp at IH; apply IH; rfl
    apply Hτv; apply HwellBinds
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
    intros _ _ _ _ _ _ _ _ _ _ _ _ IHf IHarg Δ HEqΓ Hτv
    apply typing.app₁
    apply IHf; apply HEqΓ; apply Hτv
    apply IHarg; apply HEqΓ; apply Hτv
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ _ IHf IHarg Δ HEqΓ Hτv
    apply typing.app₂
    apply IHf; apply HEqΓ; apply Hτv
    apply IHarg; apply HEqΓ; apply Hτv
  case binary₁ =>
    intros _ _ _ _ _ _ _ _ _ _ IHl IHr Δ HEqΓ Hτv
    apply typing.binary₁
    apply IHl; apply HEqΓ; apply Hτv
    apply IHr; apply HEqΓ; apply Hτv
  case binary₂ =>
    intros _ _ _ _ _ _ _ _ _ IHl IHr Δ HEqΓ Hτv
    apply typing.binary₂
    apply IHl; apply HEqΓ; apply Hτv
    apply IHr; apply HEqΓ; apply Hτv
  case lit₁ => intros; apply typing.lit₁
  case lift_lit =>
    intros _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.lift_lit
    apply IH; apply HEqΓ; apply Hτv
  case code_fragment =>
    intros _ _ x _ Hbinds HwellBinds Δ HEqΓ Hτv
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
    intros _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.code_rep
    apply IH; apply HEqΓ; apply Hτv
  case reflect =>
    intros _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.reflect
    apply IH; apply HEqΓ; apply Hτv
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe Δ HEqΓ Hτv
    rw [HEqΓ] at IHb; rw [HEqΓ] at IHe; rw [HEqΓ] at Hclose
    rw [subst_open₀_comm, shiftr_open₀_comm] at IHe
    simp at IHb; simp at IHe
    apply typing.lets
    apply IHb; apply Hτv
    simp; rw [← List.cons_append]; apply IHe; rfl
    apply Hτv; apply HwellBinds
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
    intros _ _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe Δ HEqΓ Hτv
    rw [HEqΓ] at IHb; rw [HEqΓ] at IHe; rw [HEqΓ] at Hclose
    rw [subst_open₀_comm, shiftr_open₀_comm] at IHe
    simp at IHb; simp at IHe
    apply typing.let𝕔
    apply IHb; apply Hτv
    simp; rw [← List.cons_append]; apply IHe; rfl
    apply Hτv; apply HwellBinds
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
  case run =>
    intros _ _ _ _ _ _ Hclose IH Δ HEqΓ Hτv
    apply typing.run
    apply IH; apply HEqΓ; apply Hτv
    rw [shiftr_id, subst_closed_id]; apply Hclose
    apply closed_inc; apply Hclose; omega
    rw [subst_closed_id]
    apply closed_inc; apply Hclose; omega
    apply closed_inc; apply Hclose; omega
  case loc =>
    intros _ _ _ HbindsLoc Δ HEqΓ Hτv
    apply typing.loc
    apply HbindsLoc
  case load₁ =>
    intros _ _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.load₁
    apply IH; apply HEqΓ; apply Hτv
  case alloc₁ =>
    intros _ _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.alloc₁
    apply IH; apply HEqΓ; apply Hτv
  case store₁ =>
    intros _ _ _ _ _ _ _ _ _ IHl IHr Δ HEqΓ Hτv
    apply typing.store₁
    apply IHl; apply HEqΓ; apply Hτv
    apply IHr; apply HEqΓ; apply Hτv
  case load₂ =>
    intros _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.load₂
    apply IH; apply HEqΓ; apply Hτv
  case alloc₂ =>
    intros _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.alloc₂
    apply IH; apply HEqΓ; apply Hτv
  case store₂ =>
    intros _ _ _ _ _ _ _ _ IHl IHr Δ HEqΓ Hτv
    apply typing.store₂
    apply IHl; apply HEqΓ; apply Hτv
    apply IHr; apply HEqΓ; apply Hτv
  case ifz₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ _ IHc IHl IHr Δ HEqΓ Hτv
    apply typing.ifz₁
    apply IHc; apply HEqΓ; apply Hτv
    apply IHl; apply HEqΓ; apply Hτv
    apply IHr; apply HEqΓ; apply Hτv
  case ifz₂ =>
    intros _ _ _ _ _ _ _ _ _ _ _ _ IHc IHl IHr Δ HEqΓ Hτv
    apply typing.ifz₂
    apply IHc; apply HEqΓ; apply Hτv
    apply IHl; apply HEqΓ; apply Hτv
    apply IHr; apply HEqΓ; apply Hτv
  case fix₁ =>
    intros _ _ _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.fix₁
    apply IH; apply HEqΓ; apply Hτv
  case pure =>
    intros _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing_reification.pure
    apply IH; apply HEqΓ; apply Hτv
  case reify =>
    intros _ _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing_reification.reify
    apply IH; apply HEqΓ; apply Hτv
  apply Hτe

theorem preservation_subst :
  ∀ Γ σ v e τ𝕒 τ𝕓 φ,
    typing Γ σ .stat v τ𝕒 ∅ →
    typing ((τ𝕒, .stat) :: Γ) σ .stat e τ𝕓 φ →
    typing Γ σ .stat (subst Γ.length v e) τ𝕓 φ :=
  by
  intros Γ σ v e τ𝕒 τ𝕓 φ Hτv Hτe
  have H := preservation_subst_strengthened ((τ𝕒, .stat) :: Γ) [] Γ σ v e τ𝕒 τ𝕓 φ
  simp at H
  have H := H Hτe Hτv
  rw [shiftr_id] at H
  apply H
  apply subst_closed_at
  apply closed_inc; apply typing_closed; apply Hτv; omega
  rw [← List.length_cons]; apply typing_closed; apply Hτe

theorem preservation_maping_strengthened :
  ∀ Δ Φ σ v e τ𝕒 τ𝕓 τ𝕔 𝕊𝕒 φ,
    typing (Δ ++ (τ𝕔, .stat) :: Φ) σ .stat e τ𝕓 φ →
    typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) σ .stat v τ𝕔 ∅ →
    typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) σ .stat (subst Φ.length v e) τ𝕓 φ :=
  by
  intros Δ Φ σ v e τ𝕒 τ𝕓 τ𝕔 𝕊𝕒 φ
  generalize HEqΓ : Δ ++ (τ𝕔, .stat) :: Φ = Γ
  intros Hτe Hτv
  revert Δ
  apply
    @typing.rec
      (fun Γ σ 𝕊 e τ𝕓 φ (H : typing Γ σ 𝕊 e τ𝕓 φ) =>
        ∀ Δ,
          Δ ++ (τ𝕔, .stat) :: Φ = Γ →
          typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) σ .stat v τ𝕔 ∅ →
          typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) σ 𝕊 (subst Φ.length v e) τ𝕓 φ)
      (fun Γ σ e τ𝕓 φ (H : typing_reification Γ σ e τ𝕓 φ) =>
        ∀ Δ,
          Δ ++ (τ𝕔, .stat) :: Φ = Γ →
          typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) σ .stat v τ𝕔 ∅ →
          typing_reification (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) σ (subst Φ.length v e) τ𝕓 φ)
  case fvar =>
    intros _ _ 𝕊 x _ Hbinds HwellBinds Δ HEqΓ Hτv
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
    intros _ _ _ _ _ _ _ _ HwellBinds Hclose IH Δ HEqΓ Hτv
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
    intros _ _ _ _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.lift_lam
    apply IH; apply HEqΓ; apply Hτv
  case lam𝕔 =>
    intros _ _ _ _ _ _ _ HwellBinds Hclose IH Δ HEqΓ Hτv
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
    intros _ _ _ _ _ _ _ _ _ _ _ _ IHf IHarg Δ HEqΓ Hτv
    apply typing.app₁
    apply IHf; apply HEqΓ; apply Hτv
    apply IHarg; apply HEqΓ; apply Hτv
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ _ IHf IHarg Δ HEqΓ Hτv
    apply typing.app₂
    apply IHf; apply HEqΓ; apply Hτv
    apply IHarg; apply HEqΓ; apply Hτv
  case binary₁ =>
    intros _ _ _ _ _ _ _ _ _ _ IHl IHr Δ HEqΓ Hτv
    apply typing.binary₁
    apply IHl; apply HEqΓ; apply Hτv
    apply IHr; apply HEqΓ; apply Hτv
  case binary₂ =>
    intros _ _ _ _ _ _ _ _ _ IHl IHr Δ HEqΓ Hτv
    apply typing.binary₂
    apply IHl; apply HEqΓ; apply Hτv
    apply IHr; apply HEqΓ; apply Hτv
  case lit₁ => intros; apply typing.lit₁
  case lift_lit =>
    intros _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.lift_lit
    apply IH; apply HEqΓ; apply Hτv
  case code_fragment =>
    intros _ _ x _ Hbinds HwellBinds Δ HEqΓ Hτv
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
    intros _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.code_rep
    apply IH; apply HEqΓ; apply Hτv
  case reflect =>
    intros _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.reflect
    apply IH; apply HEqΓ; apply Hτv
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe Δ HEqΓ Hτv
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
    intros _ _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe Δ HEqΓ Hτv
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
  case run =>
    intros _ _ _ _ _ _ Hclose IH Δ HEqΓ Hτv
    apply typing.run
    apply IH; apply HEqΓ; apply Hτv
    rw [subst_closed_id]; apply Hclose
    apply closed_inc; apply Hclose; omega
  case loc =>
    intros _ _ _ HbindsLoc Δ HEqΓ Hτv
    apply typing.loc
    apply HbindsLoc
  case load₁ =>
    intros _ _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.load₁
    apply IH; apply HEqΓ; apply Hτv
  case alloc₁ =>
    intros _ _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.alloc₁
    apply IH; apply HEqΓ; apply Hτv
  case store₁ =>
    intros _ _ _ _ _ _ _ _ _ IHl IHr Δ HEqΓ Hτv
    apply typing.store₁
    apply IHl; apply HEqΓ; apply Hτv
    apply IHr; apply HEqΓ; apply Hτv
  case load₂ =>
    intros _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.load₂
    apply IH; apply HEqΓ; apply Hτv
  case alloc₂ =>
    intros _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.alloc₂
    apply IH; apply HEqΓ; apply Hτv
  case store₂ =>
    intros _ _ _ _ _ _ _ _ IHl IHr Δ HEqΓ Hτv
    apply typing.store₂
    apply IHl; apply HEqΓ; apply Hτv
    apply IHr; apply HEqΓ; apply Hτv
  case ifz₁ =>
    intros _ _ _ _ _ _ _ _ _ _ _ _ IHc IHl IHr Δ HEqΓ Hτv
    apply typing.ifz₁
    apply IHc; apply HEqΓ; apply Hτv
    apply IHl; apply HEqΓ; apply Hτv
    apply IHr; apply HEqΓ; apply Hτv
  case ifz₂ =>
    intros _ _ _ _ _ _ _ _ _ _ _ _ IHc IHl IHr Δ HEqΓ Hτv
    apply typing.ifz₂
    apply IHc; apply HEqΓ; apply Hτv
    apply IHl; apply HEqΓ; apply Hτv
    apply IHr; apply HEqΓ; apply Hτv
  case fix₁ =>
    intros _ _ _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing.fix₁
    apply IH; apply HEqΓ; apply Hτv
  case pure =>
    intros _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing_reification.pure
    apply IH; apply HEqΓ; apply Hτv
  case reify =>
    intros _ _ _ _ _ _ IH Δ HEqΓ Hτv
    apply typing_reification.reify
    apply IH; apply HEqΓ; apply Hτv
  apply Hτe

theorem preservation_maping :
  ∀ Γ σ v e τ𝕒 τ𝕓 τ𝕔 𝕊𝕒 φ,
    typing ((τ𝕔, .stat) :: Γ) σ .stat e τ𝕓 φ →
    typing ((τ𝕒, 𝕊𝕒) :: Γ) σ .stat v τ𝕔 ∅ →
    typing ((τ𝕒, 𝕊𝕒) :: Γ) σ .stat (subst Γ.length v e) τ𝕓 φ := by
  intros Γ σ v e τ𝕒 τ𝕓 τ𝕔 𝕊𝕒 φ
  rw [← List.nil_append ((τ𝕔, .stat) :: Γ), ← List.nil_append ((τ𝕒, 𝕊𝕒) :: Γ)]
  apply preservation_maping_strengthened
