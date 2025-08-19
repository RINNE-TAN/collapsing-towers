import CollapsingTowers.TwoLevelRec.SyntacticTyping.Weakening
import CollapsingTowers.TwoLevelRec.SyntacticTyping.Shrinking

lemma preservation.static_subst.strengthened :
  ∀ Γ Δ Φ v e τ𝕒 τ𝕓 φ,
    typing Γ 𝟙 e τ𝕓 φ →
    Γ = Δ ++ (τ𝕒, 𝟙) :: Φ →
    typing Φ 𝟙 v τ𝕒 ⊥ →
    typing (Δ ++ Φ) 𝟙 (shiftr Φ.length (subst Φ.length v e)) τ𝕓 φ :=
  by
  generalize HEq𝕊 : 𝟙 = 𝕊
  intros Γ Δ Φ v e τ𝕒 τ𝕓 φ Hτe HEqΓ
  revert Δ HEq𝕊
  apply
    @typing.rec
      (fun Γ 𝕊 e τ𝕓 φ (H : typing Γ 𝕊 e τ𝕓 φ) =>
        𝟙 = 𝕊 →
        ∀ Δ,
          Γ = Δ ++ (τ𝕒, 𝕊) :: Φ →
          typing Φ 𝕊 v τ𝕒 ⊥ →
          typing (Δ ++ Φ) 𝕊 (shiftr Φ.length (subst Φ.length v e)) τ𝕓 φ)
      (fun Γ e τ𝕓 φ (H : typing_reification Γ e τ𝕓 φ) => true)
  <;> (intros; try contradiction)
  case fvar 𝕊 x _ HBinds Hwbt HEq𝕊 Δ HEqΓ Hτv =>
    rw [HEqΓ] at HBinds
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      simp [if_neg (Nat.ne_of_lt Hx), ← apply_ite]
      apply typing.fvar
      . apply fvar.shrinking
        omega; apply HBinds
      . apply Hwbt
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      have HBinds := binds.shrink _ _ _ _ (by simp; omega) HBinds
      simp [if_pos Hx]; simp [← Hx] at HBinds
      rw [identity.shiftr, ← HBinds]
      apply typing.weakening; apply Hτv
      apply closed.inc; apply typing.closed_at_env _ _ _ _ _ Hτv; omega
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      simp [if_neg (Nat.ne_of_gt Hx), ← apply_ite]
      apply typing.fvar
      . apply fvar.shrinking
        omega; apply HBinds
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
  case binary₁ IHl IHr HEq𝕊 Δ HEqΓ Hτv =>
    apply typing.binary₁
    . apply IHl; apply HEq𝕊; apply HEqΓ; apply Hτv
    . apply IHr; apply HEq𝕊; apply HEqΓ; apply Hτv
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
  case fix₁ Hfixφ _ IH HEq𝕊 Δ HEqΓ Hτv =>
    apply typing.fix₁
    . apply Hfixφ
    . apply IH; apply HEq𝕊; apply HEqΓ; apply Hτv
  case ifz₁ IHc IHl IHr HEq𝕊 Δ HEqΓ Hτv =>
    apply typing.ifz₁
    . apply IHc; apply HEq𝕊; apply HEqΓ; apply Hτv
    . apply IHl; apply HEq𝕊; apply HEqΓ; apply Hτv
    . apply IHr; apply HEq𝕊; apply HEqΓ; apply Hτv
  case pure => simp
  case reify => simp
  apply Hτe

theorem preservation.static_subst :
  ∀ Γ v e τ𝕒 τ𝕓,
    typing Γ 𝟙 v τ𝕒 ⊥ →
    typing ((τ𝕒, 𝟙) :: Γ) 𝟙 e τ𝕓 ⊥ →
    typing Γ 𝟙 (subst Γ.length v e) τ𝕓 ⊥ :=
  by
  intros Γ v e τ𝕒 τ𝕓 Hτv Hτe
  have H := preservation.static_subst.strengthened ((τ𝕒, 𝟙) :: Γ) [] Γ v e τ𝕒 τ𝕓 ⊥ Hτe rfl Hτv
  rw [identity.shiftr] at H; apply H
  apply closed.under_subst
  apply closed.inc; apply typing.closed_at_env; apply Hτv; omega
  rw [← List.length_cons]; apply typing.closed_at_env; apply Hτe
