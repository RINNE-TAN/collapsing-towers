import Instar.TwoLevelBasic.SyntacticTyping.Defs

lemma preservation.dynamic_subst.strengthened :
  ∀ Γ Δ Φ v e τ𝕒 τ𝕓 ε,
    typing Γ 𝟚 e τ𝕓 ε →
    Γ = Δ ++ (τ𝕒, 𝟚) :: Φ →
    typing Φ 𝟚 v τ𝕒 ⊥ →
    typing (Δ ++ Φ) 𝟚 (shiftr Φ.length (subst Φ.length v e)) τ𝕓 ε :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Γ Δ Φ v e τ𝕒 τ𝕓 ε Hτe HEqΓ
  revert Δ HEq𝕊
  apply
    @typing.rec
      (fun Γ 𝕊 e τ𝕓 ε (H : typing Γ 𝕊 e τ𝕓 ε) =>
        𝟚 = 𝕊 →
        ∀ Δ,
          Γ = Δ ++ (τ𝕒, 𝕊) :: Φ →
          typing Φ 𝕊 v τ𝕒 ⊥ →
          typing (Δ ++ Φ) 𝕊 (shiftr Φ.length (subst Φ.length v e)) τ𝕓 ε)
      (fun Γ e τ𝕓 ε (H : typing_reification Γ e τ𝕓 ε) => true)
  <;> (intros; try contradiction)
  case fvar 𝕊 x _ Hbinds Hwbt HEq𝕊 Δ HEqΓ Hτv =>
    rw [HEqΓ] at Hbinds
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      simp [if_neg (Nat.ne_of_lt Hx), ← apply_ite]
      apply typing.fvar
      . apply fvar.shrinking
        omega; apply Hbinds
      . apply Hwbt
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      have Hbinds := binds.shrink _ _ _ _ (by simp; omega) Hbinds
      simp [if_pos Hx]; simp [← Hx] at Hbinds
      rw [identity.shiftr, ← Hbinds]
      apply typing.weakening; apply Hτv
      apply closed.inc; apply typing.closed_at_env _ _ _ _ _ Hτv; omega
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      simp [if_neg (Nat.ne_of_gt Hx), ← apply_ite]
      apply typing.fvar
      . apply fvar.shrinking
        omega; apply Hbinds
      . apply Hwbt
  case lam 𝕊 _ _ _ _ _ Hwbt Hclosed IH HEq𝕊 Δ HEqΓ Hτv =>
    simp [HEqΓ] at Hclosed
    rw [HEqΓ] at IH
    apply typing.lam
    . have HEq : (Δ ++ Φ).length = (Δ ++ (τ𝕒, 𝕊) :: Φ).length - 1 := by simp
      rw [HEq, ← comm.shiftr_opening, ← comm.subst_opening]
      apply IH HEq𝕊 (_ :: Δ) rfl Hτv
      . simp; omega
      . apply typing.regular _ _ _ _ _ Hτv
      . simp; omega
    . apply Hwbt
    . simp
      apply closed.dec.under_shiftr
      apply closed.under_subst
      . apply closed.inc
        apply typing.closed_at_env _ _ _ _ _ Hτv; omega
      . apply Hclosed
      . apply not_in_fv.under_subst
        apply closed_impl_not_in_fv
        apply typing.closed_at_env _ _ _ _ _ Hτv; omega
  case app₁ IHf IHarg HEq𝕊 Δ HEqΓ Hτv =>
    apply typing.app₁
    . apply IHf; apply HEq𝕊; apply HEqΓ; apply Hτv
    . apply IHarg; apply HEq𝕊; apply HEqΓ; apply Hτv
  case lit => apply typing.lit
  case lets 𝕊 _ _ _ _ _ _ _ _ Hwbt Hclosed IHb IHe HEq𝕊 Δ HEqΓ Hτv =>
    simp [HEqΓ] at Hclosed
    rw [HEqΓ] at IHe
    apply typing.lets
    . apply IHb; apply HEq𝕊; apply HEqΓ; apply Hτv
    . have HEq : (Δ ++ Φ).length = (Δ ++ (τ𝕒, 𝕊) :: Φ).length - 1 := by simp
      rw [HEq, ← comm.shiftr_opening, ← comm.subst_opening]
      apply IHe HEq𝕊 (_ :: Δ) rfl Hτv
      . simp; omega
      . apply typing.regular _ _ _ _ _ Hτv
      . simp; omega
    . apply Hwbt
    . simp
      apply closed.dec.under_shiftr
      apply closed.under_subst
      . apply closed.inc
        apply typing.closed_at_env _ _ _ _ _ Hτv; omega
      . apply Hclosed
      . apply not_in_fv.under_subst
        apply closed_impl_not_in_fv
        apply typing.closed_at_env _ _ _ _ _ Hτv; omega
  case pure => simp
  case reify => simp
  apply Hτe

theorem preservation.dynamic_subst :
  ∀ Γ v e τ𝕒 τ𝕓,
    typing Γ 𝟚 v τ𝕒 ⊥ →
    typing ((τ𝕒, 𝟚) :: Γ) 𝟚 e τ𝕓 ⊥ →
    typing Γ 𝟚 (subst Γ.length v e) τ𝕓 ⊥ :=
  by
  intros Γ v e τ𝕒 τ𝕓 Hτv Hτe
  have H := preservation.dynamic_subst.strengthened ((τ𝕒, 𝟚) :: Γ) ⦰ Γ v e τ𝕒 τ𝕓 ⊥ Hτe rfl Hτv
  rw [identity.shiftr] at H; apply H
  apply closed.under_subst
  apply closed.inc; apply typing.closed_at_env; apply Hτv; omega
  rw [← List.length_cons]; apply typing.closed_at_env; apply Hτe

lemma preservation.subst.strengthened :
  ∀ Γ Δ Φ 𝕊 v e τ𝕒 τ𝕓 ε,
    typing Γ 𝕊 e τ𝕓 ε →
    Γ = Δ ++ (τ𝕒, 𝟙) :: Φ →
    typing Φ 𝟙 v τ𝕒 ⊥ →
    typing (Δ ++ Φ) 𝕊 (shiftr Φ.length (subst Φ.length v e)) τ𝕓 ε :=
  by
  intros Γ Δ Φ 𝕊 v e τ𝕒 τ𝕓 ε Hτe HEqΓ
  revert Δ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ𝕓 ε (H : typing Γ 𝕊 e τ𝕓 ε) =>
        ∀ Δ,
          Γ = Δ ++ (τ𝕒, 𝟙) :: Φ →
          typing Φ 𝟙 v τ𝕒 ⊥ →
          typing (Δ ++ Φ) 𝕊 (shiftr Φ.length (subst Φ.length v e)) τ𝕓 ε)
      (fun Γ e τ𝕓 ε (H : typing_reification Γ e τ𝕓 ε) =>
        ∀ Δ,
          Γ = Δ ++ (τ𝕒, 𝟙) :: Φ →
          typing Φ 𝟙 v τ𝕒 ⊥ →
          typing_reification (Δ ++ Φ) (shiftr Φ.length (subst Φ.length v e)) τ𝕓 ε)
  <;> intros
  case fvar 𝕊 x _ Hbinds Hwbt Δ HEqΓ Hτv =>
    rw [HEqΓ] at Hbinds
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      simp [if_neg (Nat.ne_of_lt Hx), ← apply_ite]
      apply typing.fvar
      . apply fvar.shrinking
        omega; apply Hbinds
      . apply Hwbt
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      have Hbinds := binds.shrink _ _ _ _ (by simp; omega) Hbinds
      simp [if_pos Hx]; simp [← Hx] at Hbinds
      rw [identity.shiftr]; simp [← Hbinds]
      apply typing.weakening; apply Hτv
      apply closed.inc; apply typing.closed_at_env _ _ _ _ _ Hτv; omega
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      simp [if_neg (Nat.ne_of_gt Hx), ← apply_ite]
      apply typing.fvar
      . apply fvar.shrinking
        omega; apply Hbinds
      . apply Hwbt
  case code_fragment x _ Hbinds Hwbt Δ HEqΓ Hτv =>
    rw [HEqΓ] at Hbinds
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      simp [if_neg (Nat.ne_of_lt Hx), ← apply_ite]
      apply typing.code_fragment
      . apply fvar.shrinking
        omega; apply Hbinds
      . apply Hwbt
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      have Hbinds := binds.shrink _ _ _ _ (by simp; omega) Hbinds
      simp [← Hx] at Hbinds
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      simp [if_neg (Nat.ne_of_gt Hx), ← apply_ite]
      apply typing.code_fragment
      . apply fvar.shrinking
        omega; apply Hbinds
      . apply Hwbt
  case lam Hwbt Hclosed IH Δ HEqΓ Hτv =>
    simp [HEqΓ] at Hclosed
    rw [HEqΓ] at IH
    apply typing.lam
    . have HEq : (Δ ++ Φ).length = (Δ ++ (τ𝕒, 𝟙) :: Φ).length - 1 := by simp
      rw [HEq, ← comm.shiftr_opening, ← comm.subst_opening]
      apply IH (_ :: Δ) rfl Hτv
      . simp; omega
      . apply typing.regular _ _ _ _ _ Hτv
      . simp; omega
    . apply Hwbt
    . simp
      apply closed.dec.under_shiftr
      apply closed.under_subst
      . apply closed.inc
        apply typing.closed_at_env _ _ _ _ _ Hτv; omega
      . apply Hclosed
      . apply not_in_fv.under_subst
        apply closed_impl_not_in_fv
        apply typing.closed_at_env _ _ _ _ _ Hτv; omega
  case lam𝕔 Hwbt Hclosed IH Δ HEqΓ Hτv =>
    simp [HEqΓ] at Hclosed
    rw [HEqΓ] at IH
    apply typing.lam𝕔
    . have HEq : (Δ ++ Φ).length = (Δ ++ (τ𝕒, 𝟙) :: Φ).length - 1 := by simp
      rw [HEq, ← comm.shiftr_opening, ← comm.subst_opening]
      apply IH (_ :: Δ) rfl Hτv
      . simp; omega
      . apply typing.regular _ _ _ _ _ Hτv
      . simp; omega
    . apply Hwbt
    . simp
      apply closed.dec.under_shiftr
      apply closed.under_subst
      . apply closed.inc
        apply typing.closed_at_env _ _ _ _ _ Hτv; omega
      . apply Hclosed
      . apply not_in_fv.under_subst
        apply closed_impl_not_in_fv
        apply typing.closed_at_env _ _ _ _ _ Hτv; omega
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
  case lets 𝕊 Hwbt Hclosed IHb IHe Δ HEqΓ Hτv =>
    simp [HEqΓ] at Hclosed
    rw [HEqΓ] at IHe
    apply typing.lets
    . apply IHb; apply HEqΓ; apply Hτv
    . have HEq : (Δ ++ Φ).length = (Δ ++ (τ𝕒, 𝟙) :: Φ).length - 1 := by simp
      rw [HEq, ← comm.shiftr_opening, ← comm.subst_opening]
      apply IHe (_ :: Δ) rfl Hτv
      . simp; omega
      . apply typing.regular _ _ _ _ _ Hτv
      . simp; omega
    . apply Hwbt
    . simp
      apply closed.dec.under_shiftr
      apply closed.under_subst
      . apply closed.inc
        apply typing.closed_at_env _ _ _ _ _ Hτv; omega
      . apply Hclosed
      . apply not_in_fv.under_subst
        apply closed_impl_not_in_fv
        apply typing.closed_at_env _ _ _ _ _ Hτv; omega
  case lets𝕔 𝕊 Hwbt Hclosed IHb IHe Δ HEqΓ Hτv =>
    simp [HEqΓ] at Hclosed
    rw [HEqΓ] at IHe
    apply typing.lets𝕔
    . apply IHb; apply HEqΓ; apply Hτv
    . have HEq : (Δ ++ Φ).length = (Δ ++ (τ𝕒, 𝟙) :: Φ).length - 1 := by simp
      rw [HEq, ← comm.shiftr_opening, ← comm.subst_opening]
      apply IHe (_ :: Δ) rfl Hτv
      . simp; omega
      . apply typing.regular _ _ _ _ _ Hτv
      . simp; omega
    . apply Hwbt
    . simp
      apply closed.dec.under_shiftr
      apply closed.under_subst
      . apply closed.inc
        apply typing.closed_at_env _ _ _ _ _ Hτv; omega
      . apply Hclosed
      . apply not_in_fv.under_subst
        apply closed_impl_not_in_fv
        apply typing.closed_at_env _ _ _ _ _ Hτv; omega
  case run Hclosed IH Δ HEqΓ Hτv =>
    apply typing.run
    . apply IH; apply HEqΓ; apply Hτv
    . rw [identity.shiftr, identity.subst]; apply Hclosed
      apply closed.inc; apply Hclosed; omega
      rw [identity.subst]
      apply closed.inc; apply Hclosed; omega
      apply closed.inc; apply Hclosed; omega
  case pure IH Δ HEqΓ Hτv =>
    apply typing_reification.pure
    apply IH; apply HEqΓ; apply Hτv
  case reify IH Δ HEqΓ Hτv =>
    apply typing_reification.reify
    apply IH; apply HEqΓ; apply Hτv
  apply Hτe

theorem preservation.subst :
  ∀ Γ 𝕊 v e τ𝕒 τ𝕓 ε,
    typing Γ 𝟙 v τ𝕒 ⊥ →
    typing ((τ𝕒, 𝟙) :: Γ) 𝕊 e τ𝕓 ε →
    typing Γ 𝕊 (subst Γ.length v e) τ𝕓 ε :=
  by
  intros Γ 𝕊 v e τ𝕒 τ𝕓 ε Hτv Hτe
  have H := preservation.subst.strengthened ((τ𝕒, 𝟙) :: Γ) ⦰ Γ 𝕊 v e τ𝕒 τ𝕓 ε Hτe rfl Hτv
  rw [identity.shiftr] at H; apply H
  apply closed.under_subst
  apply closed.inc; apply typing.closed_at_env; apply Hτv; omega
  rw [← List.length_cons]; apply typing.closed_at_env; apply Hτe
