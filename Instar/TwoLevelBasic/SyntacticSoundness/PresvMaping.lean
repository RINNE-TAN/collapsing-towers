import Instar.TwoLevelBasic.SyntacticTyping.Defs

lemma preservation.maping.strengthened :
  ∀ Γ Δ Φ v e τ𝕒 τ𝕓 τ𝕔 𝕊𝕒 𝕊𝕓 ε,
    typing Γ 𝕊𝕓 e τ𝕓 ε →
    Γ = Δ ++ (τ𝕔, 𝟙) :: Φ →
    typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) 𝟙 v τ𝕔 ⊥ →
    typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) 𝕊𝕓 (subst Φ.length v e) τ𝕓 ε :=
  by
  intros Γ Δ Φ v e τ𝕒 τ𝕓 τ𝕔 𝕊𝕒 𝕊𝕓 ε Hτe HEqΓ Hτv
  revert Δ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ𝕓 ε (H : typing Γ 𝕊 e τ𝕓 ε) =>
        ∀ Δ,
          Γ = Δ ++ (τ𝕔, 𝟙) :: Φ →
          typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) 𝟙 v τ𝕔 ⊥ →
          typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) 𝕊 (subst Φ.length v e) τ𝕓 ε)
      (fun Γ e τ𝕓 ε (H : typing_reification Γ e τ𝕓 ε) =>
        ∀ Δ,
          Γ = Δ ++ (τ𝕔, 𝟙) :: Φ →
          typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) 𝟙 v τ𝕔 ⊥ →
          typing_reification (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) (subst Φ.length v e) τ𝕓 ε)
  <;> intros
  case fvar 𝕊 x _ Hbinds Hwbt Δ HEqΓ Hτv =>
    rw [HEqΓ] at Hbinds
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      simp [if_neg (Nat.ne_of_lt Hx)]
      apply typing.fvar
      . have HEq : x = x - ((τ𝕔, 𝟙) :: Φ).length + ((τ𝕒, 𝕊𝕒) :: Φ).length := by simp; omega
        rw [HEq]
        apply binds.extendr
        apply binds.shrinkr
        have HEq : x - ((τ𝕔, 𝟙) :: Φ).length + ((τ𝕔, 𝟙) :: Φ).length = x := by simp; omega
        rw [HEq]
        apply Hbinds
      . apply Hwbt
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      have Hbinds := binds.shrink _ _ _ _ (by simp; omega) Hbinds
      simp [← Hx] at Hbinds
      simp [if_pos Hx, ← Hbinds]
      apply Hτv
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      simp [if_neg (Nat.ne_of_gt Hx)]
      apply typing.fvar
      . rw [List.append_cons]
        rw [List.append_cons] at Hbinds
        apply binds.extend
        apply binds.shrink; omega
        apply Hbinds
      . apply Hwbt
  case code_fragment x _ Hbinds Hwbt Δ HEqΓ Hτv =>
    rw [HEqΓ] at Hbinds
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      simp [if_neg (Nat.ne_of_lt Hx)]
      apply typing.code_fragment
      . have HEq : x = x - ((τ𝕔, 𝟙) :: Φ).length + ((τ𝕒, 𝕊𝕒) :: Φ).length := by simp; omega
        rw [HEq]
        apply binds.extendr
        apply binds.shrinkr
        have HEq : x - ((τ𝕔, 𝟙) :: Φ).length + ((τ𝕔, 𝟙) :: Φ).length = x := by simp; omega
        rw [HEq]
        apply Hbinds
      . apply Hwbt
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      have Hbinds := binds.shrink _ _ _ _ (by simp; omega) Hbinds
      simp [← Hx] at Hbinds
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      simp [if_neg (Nat.ne_of_gt Hx)]
      apply typing.code_fragment
      . rw [List.append_cons]
        rw [List.append_cons] at Hbinds
        apply binds.extend
        apply binds.shrink; omega
        apply Hbinds
      . apply Hwbt
  case lam Hwbt Hclosed IH Δ HEqΓ Hτv =>
    simp [HEqΓ] at Hclosed
    rw [HEqΓ] at IH
    apply typing.lam
    . have HEq : (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ).length = (Δ ++ (τ𝕔, 𝟙) :: Φ).length := by simp
      rw [HEq, ← comm.subst_opening]
      apply IH (_ :: Δ) rfl
      apply typing.weakening.singleton _ _ _ _ _ _ Hτv
      simp; omega
      apply typing.regular _ _ _ _ _ Hτv
    . apply Hwbt
    . apply closed.under_subst
      . apply typing.closed_at_env _ _ _ _ _ Hτv
      . simp; apply Hclosed
  case lam𝕔 Hwbt Hclosed IH Δ HEqΓ Hτv =>
    simp [HEqΓ] at Hclosed
    rw [HEqΓ] at IH
    apply typing.lam𝕔
    . have HEq : (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ).length = (Δ ++ (τ𝕔, 𝟙) :: Φ).length := by simp
      rw [HEq, ← comm.subst_opening]
      apply IH (_ :: Δ) rfl
      apply typing.weakening.singleton _ _ _ _ _ _ Hτv
      simp; omega
      apply typing.regular _ _ _ _ _ Hτv
    . apply Hwbt
    . apply closed.under_subst
      . apply typing.closed_at_env _ _ _ _ _ Hτv
      . simp; apply Hclosed
  case lift_lam IH Δ HEqΓ Hτv =>
    apply typing.lift_lam
    apply IH; apply HEqΓ; apply Hτv
  case app₁ IHf IHarg Δ HEqΓ Hτv =>
    apply typing.app₁
    . apply IHf; apply HEqΓ; apply Hτv
    . apply IHarg; apply HEqΓ; apply Hτv
  case app₂ IHf IHarg Δ HEqΓ Hτv =>
    apply typing.app₂
    . apply IHf; apply HEqΓ; apply Hτv
    . apply IHarg; apply HEqΓ; apply Hτv
  case lit => apply typing.lit
  case lift_lit IH Δ HEqΓ Hτv =>
    apply typing.lift_lit
    apply IH; apply HEqΓ; apply Hτv
  case code_rep IH Δ HEqΓ Hτv =>
    apply typing.code_rep
    apply IH; apply HEqΓ; apply Hτv
  case reflect IH Δ HEqΓ Hτv =>
    apply typing.reflect
    apply IH; apply HEqΓ; apply Hτv
  case lets Hwbt Hclosed IHb IHe Δ HEqΓ Hτv =>
    simp [HEqΓ] at Hclosed
    rw [HEqΓ] at IHe
    apply typing.lets
    . apply IHb; apply HEqΓ; apply Hτv
    . have HEq : (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ).length = (Δ ++ (τ𝕔, 𝟙) :: Φ).length := by simp
      rw [HEq, ← comm.subst_opening]
      apply IHe (_ :: Δ) rfl
      apply typing.weakening.singleton _ _ _ _ _ _ Hτv
      simp; omega
      apply typing.regular _ _ _ _ _ Hτv
    . apply Hwbt
    . apply closed.under_subst
      . apply typing.closed_at_env _ _ _ _ _ Hτv
      . simp; apply Hclosed
  case lets𝕔 Hwbt Hclosed IHb IHe Δ HEqΓ Hτv =>
    simp [HEqΓ] at Hclosed
    rw [HEqΓ] at IHe
    apply typing.lets𝕔
    . apply IHb; apply HEqΓ; apply Hτv
    . have HEq : (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ).length = (Δ ++ (τ𝕔, 𝟙) :: Φ).length := by simp
      rw [HEq, ← comm.subst_opening]
      apply IHe (_ :: Δ) rfl
      apply typing.weakening.singleton _ _ _ _ _ _ Hτv
      simp; omega
      apply typing.regular _ _ _ _ _ Hτv
    . apply Hwbt
    . apply closed.under_subst
      . apply typing.closed_at_env _ _ _ _ _ Hτv
      . simp; apply Hclosed
  case run Hclosed IH Δ HEqΓ Hτv =>
    apply typing.run
    . apply IH; apply HEqΓ; apply Hτv
    . rw [identity.subst]
      apply Hclosed
      apply closed.inc; apply Hclosed; omega
  case pure IH Δ HEqΓ Hτv =>
    apply typing_reification.pure
    apply IH; apply HEqΓ; apply Hτv
  case reify IH Δ HEqΓ Hτv =>
    apply typing_reification.reify
    apply IH; apply HEqΓ; apply Hτv
  apply Hτe

theorem preservation.maping :
  ∀ Γ v e τ𝕒 τ𝕓 τ𝕔 𝕊 ε,
    typing ((τ𝕔, 𝟙) :: Γ) 𝟙 e τ𝕓 ε →
    typing ((τ𝕒, 𝕊) :: Γ) 𝟙 v τ𝕔 ⊥ →
    typing ((τ𝕒, 𝕊) :: Γ) 𝟙 (subst Γ.length v e) τ𝕓 ε :=
  by
  intros Γ v e τ𝕒 τ𝕓 τ𝕔 𝕊 ε Hτe Hτv
  apply preservation.maping.strengthened _ ⦰ _ _ _ _ _ _ _ _ _ Hτe rfl Hτv
