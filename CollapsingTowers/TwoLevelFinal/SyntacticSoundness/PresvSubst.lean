import CollapsingTowers.TwoLevelFinal.SyntacticTyping.Defs

lemma preservation.subst.strengthened :
  ∀ Γ Δ Φ 𝕊 v e τ𝕒 τ𝕓 φ,
    typing Γ 𝕊 e τ𝕓 φ →
    Γ = Δ ++ (τ𝕒, 𝟙) :: Φ →
    typing Φ 𝟙 v τ𝕒 ⊥ →
    typing (Δ ++ Φ) 𝕊 (shiftr Φ.length (subst Φ.length v e)) τ𝕓 φ :=
  by
  intros Γ Δ Φ 𝕊 v e τ𝕒 τ𝕓 φ Hτe HEqΓ
  revert Δ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ𝕓 φ (H : typing Γ 𝕊 e τ𝕓 φ) =>
        ∀ Δ,
          Γ = Δ ++ (τ𝕒, 𝟙) :: Φ →
          typing Φ 𝟙 v τ𝕒 ⊥ →
          typing (Δ ++ Φ) 𝕊 (shiftr Φ.length (subst Φ.length v e)) τ𝕓 φ)
      (fun Γ e τ𝕓 φ (H : typing_reification Γ e τ𝕓 φ) =>
        ∀ Δ,
          Γ = Δ ++ (τ𝕒, 𝟙) :: Φ →
          typing Φ 𝟙 v τ𝕒 ⊥ →
          typing_reification (Δ ++ Φ) (shiftr Φ.length (subst Φ.length v e)) τ𝕓 φ)
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
  case lit =>
    apply typing.lit
  case lift_lit IH Δ HEqΓ Hτv =>
    apply typing.lift_lit
    apply IH; apply HEqΓ; apply Hτv
  case binary₁ IHl IHr Δ HEqΓ Hτv =>
    apply typing.binary₁
    . apply IHl; apply HEqΓ; apply Hτv
    . apply IHr; apply HEqΓ; apply Hτv
  case binary₂ IHl IHr Δ HEqΓ Hτv =>
    apply typing.binary₂
    . apply IHl; apply HEqΓ; apply Hτv
    . apply IHr; apply HEqΓ; apply Hτv
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
  case run Hsf Hclosed IH Δ HEqΓ Hτv =>
    apply typing.run
    . apply IH; apply HEqΓ; apply Hτv
    . rw [identity.shiftr, identity.subst]; apply Hsf
      apply closed.inc; apply Hclosed; omega
      rw [identity.subst]
      apply closed.inc; apply Hclosed; omega
      apply closed.inc; apply Hclosed; omega
    . rw [identity.shiftr, identity.subst]; apply Hclosed
      apply closed.inc; apply Hclosed; omega
      rw [identity.subst]
      apply closed.inc; apply Hclosed; omega
      apply closed.inc; apply Hclosed; omega
  case unit =>
    apply typing.unit
  case lift_unit IH Δ HEqΓ Hτv =>
    apply typing.lift_unit
    apply IH; apply HEqΓ; apply Hτv
  case load₁ IH Δ HEqΓ Hτv =>
    apply typing.load₁
    apply IH; apply HEqΓ; apply Hτv
  case load₂ IH Δ HEqΓ Hτv =>
    apply typing.load₂
    apply IH; apply HEqΓ; apply Hτv
  case alloc₁ IH Δ HEqΓ Hτv =>
    apply typing.alloc₁
    apply IH; apply HEqΓ; apply Hτv
  case alloc₂ IH Δ HEqΓ Hτv =>
    apply typing.alloc₂
    apply IH; apply HEqΓ; apply Hτv
  case store₁ IHl IHr Δ HEqΓ Hτv =>
    apply typing.store₁
    . apply IHl; apply HEqΓ; apply Hτv
    . apply IHr; apply HEqΓ; apply Hτv
  case store₂ IHl IHr Δ HEqΓ Hτv =>
    apply typing.store₂
    . apply IHl; apply HEqΓ; apply Hτv
    . apply IHr; apply HEqΓ; apply Hτv
  case fix₁ Hfixφ _ IH Δ HEqΓ Hτv =>
    apply typing.fix₁
    . apply Hfixφ
    . apply IH; apply HEqΓ; apply Hτv
  case fix₂ IH Δ HEqΓ Hτv =>
    apply typing.fix₂
    apply IH; apply HEqΓ; apply Hτv
  case ifz₁ IHc IHl IHr Δ HEqΓ Hτv =>
    apply typing.ifz₁
    . apply IHc; apply HEqΓ; apply Hτv
    . apply IHl; apply HEqΓ; apply Hτv
    . apply IHr; apply HEqΓ; apply Hτv
  case ifz₂ IHc IHl IHr Δ HEqΓ Hτv =>
    apply typing.ifz₂
    . apply IHc; apply HEqΓ; apply Hτv
    . apply IHl; apply HEqΓ; apply Hτv
    . apply IHr; apply HEqΓ; apply Hτv
  case pure IH Δ HEqΓ Hτv =>
    apply typing_reification.pure
    apply IH; apply HEqΓ; apply Hτv
  case reify IH Δ HEqΓ Hτv =>
    apply typing_reification.reify
    apply IH; apply HEqΓ; apply Hτv
  apply Hτe

theorem preservation.subst :
  ∀ Γ 𝕊 v e τ𝕒 τ𝕓 φ,
    typing Γ 𝟙 v τ𝕒 ⊥ →
    typing ((τ𝕒, 𝟙) :: Γ) 𝕊 e τ𝕓 φ →
    typing Γ 𝕊 (subst Γ.length v e) τ𝕓 φ :=
  by
  intros Γ 𝕊 v e τ𝕒 τ𝕓 φ Hτv Hτe
  have H := preservation.subst.strengthened ((τ𝕒, 𝟙) :: Γ) ⦰ Γ 𝕊 v e τ𝕒 τ𝕓 φ Hτe rfl Hτv
  rw [identity.shiftr] at H; apply H
  apply closed.under_subst
  apply closed.inc; apply typing.closed_at_env; apply Hτv; omega
  rw [← List.length_cons]; apply typing.closed_at_env; apply Hτe
