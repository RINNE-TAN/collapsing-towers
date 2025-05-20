
import Mathlib.Tactic
import CollapsingTowers.TwoLevel.Typing
theorem decompose𝔼 :
    ∀ size Γ E e τ𝕓,
    ctx𝔼 E ->
    typing size Γ (E e) τ𝕓 ->
    ∃ τ𝕒, typing size Γ e τ𝕒 /\ typing size (τ𝕒 :: Γ) (E (.fvar Γ.length)) τ𝕓 :=
  by
  intros size Γ E e τ𝕓 HE Hτ
  induction HE generalizing τ𝕓 with
  | hole =>
    exists τ𝕓; constructor
    apply Hτ; constructor; simp
  | cons𝔹 _ _ HB _ IHE =>
    cases HB with
    | appl₁ =>
      cases Hτ with
      | app₁ _ _ _ _ _ HτX Hτarg =>
        have ⟨τ, HτX, Hτ𝔼⟩ := IHE _ HτX
        exists τ
        constructor; apply HτX
        constructor; apply Hτ𝔼
        apply weakening1; apply Hτarg
    | appr₁ =>
      cases Hτ with
      | app₁ _ _ _ _ _ Hτv HτX =>
        have ⟨τ, HτX, Hτ𝔼⟩ := IHE _ HτX
        exists τ
        constructor; apply HτX
        constructor
        apply weakening1; apply Hτv
        apply Hτ𝔼
    | appl₂ =>
      cases Hτ with
      | app₂ _ _ _ _ _ HτX Hτarg =>
        have ⟨τ, HτX, Hτ𝔼⟩ := IHE _ HτX
        exists τ
        constructor; apply HτX
        constructor; apply Hτ𝔼
        apply weakening1; apply Hτarg
    | appr₂ =>
      cases Hτ with
      | app₂ _ _ _ _ _ Hτv HτX =>
        have ⟨τ, HτX, Hτ𝔼⟩ := IHE _ HτX
        exists τ
        constructor; apply HτX
        constructor
        apply weakening1; apply Hτv
        apply Hτ𝔼
    | plusl₁ =>
      cases Hτ with
      | plus₁ _ _ _ HτX Hτr =>
        have ⟨τ, HτX, Hτ𝔼⟩ := IHE _ HτX
        exists τ
        constructor; apply HτX
        constructor; apply Hτ𝔼
        apply weakening1; apply Hτr
    | plusr₁ =>
      cases Hτ with
      | plus₁ _ _ _ Hτv HτX =>
        have ⟨τ, HτX, Hτ𝔼⟩ := IHE _ HτX
        exists τ
        constructor; apply HτX
        constructor
        apply weakening1; apply Hτv
        apply Hτ𝔼
    | plusl₂ =>
      cases Hτ with
      | plus₂ _ _ _ HτX Hτr =>
        have ⟨τ, HτX, Hτ𝔼⟩ := IHE _ HτX
        exists τ
        constructor; apply HτX
        constructor; apply Hτ𝔼
        apply weakening1; apply Hτr
    | plusr₂ =>
      cases Hτ with
      | plus₂ _ _ _ Hτv HτX =>
        have ⟨τ, HτX, Hτ𝔼⟩ := IHE _ HτX
        exists τ
        constructor; apply HτX
        constructor
        apply weakening1; apply Hτv
        apply Hτ𝔼
    | lets e =>
      cases Hτ with
      | lets _ _ _ _ _ Hτe HτX Hclose =>
        have ⟨τ, Hτe, Hτ𝔼⟩ := IHE _ Hτe
        exists τ
        constructor; apply Hτe
        constructor; apply Hτ𝔼
        rw [List.length_cons, ← shiftl_id Γ.length e 1, ← shiftl_open₀]
        rw [← List.singleton_append, List.append_cons]
        apply weakening_strengthened
        apply HτX; rfl
        omega; apply Hclose
        apply closed_inc; apply Hclose; simp
    | lit₂ =>
      cases Hτ with
      | lit₂ _ _ HτX =>
        have ⟨τ, HτX, Hτ𝔼⟩ := IHE _ HτX
        exists τ
        constructor; apply HτX
        constructor; apply Hτ𝔼
    | lam₂ =>
      cases Hτ with
      | lam₂ _ _ _ _ HτX =>
        have ⟨τ, HτX, Hτ𝔼⟩ := IHE _ HτX
        exists τ
        constructor; apply HτX
        constructor; apply Hτ𝔼

theorem preservationℝ :
  ∀ size Γ R e₀ e₁,
  ctxℝ Γ.length R ->
  lc e₀ ->
  (∀ τ𝕒 τ𝕓, typing_strengthened size (τ𝕒 :: Γ) e₀ τ𝕓 -> typing_strengthened size (τ𝕒 :: Γ) e₁ τ𝕓) ->
  ∀ τ, typing_strengthened size Γ (R e₀) τ -> typing_strengthened size Γ (R e₁) τ :=
  by
  intro size Γ _ e₀ e₁ HR Hlc IH _ Hτe₀
  have ⟨HNeue₀, Hτe₀⟩ := Hτe₀
  cases HR with
  | lam𝕔 =>
    cases Hτe₀ with
    | lam𝕔 _ _ _ _ He _ HNeulc =>
      simp at IH HNeue₀ HNeulc
      have HNeue₀ := neutral_inc _ _ _ HNeue₀ HNeulc
      rw [open_close_id₀] at He
      rw [open_close_id] at HNeue₀
      have ⟨HNeue₁, Hτe₁⟩ := IH _ _ HNeue₀ He
      constructor
      . simp; apply neutral_closing; apply HNeue₁
      . constructor
        rw [open_close_id₀]; apply Hτe₁
        apply typing_regular; apply Hτe₁
        apply close_closed; apply typing_closed _ _ _ _ Hτe₁
        apply neutral_db_closing
        apply typing_regular; apply Hτe₁
        apply HNeue₁
      apply Hlc; apply Hlc
  | let𝕔 =>
    cases Hτe₀ with
    | let𝕔 _ _ _ _ _ Hb He _ HNeulc =>
      have ⟨HNeub, HNeue₀⟩ := HNeue₀
      simp at IH HNeue₀ HNeulc
      have HNeue₀ := neutral_inc _ _ _ HNeue₀ HNeulc
      rw [open_close_id₀] at He
      rw [open_close_id] at HNeue₀
      have ⟨HNeue₁, Hτe₁⟩ := IH _ _ HNeue₀ He
      constructor
      . constructor; apply HNeub
        apply neutral_closing; apply HNeue₁
      . constructor
        apply Hb
        rw [open_close_id₀]; apply Hτe₁
        apply typing_regular; apply Hτe₁
        apply close_closed; apply typing_closed _ _ _ _ Hτe₁
        apply neutral_db_closing
        apply typing_regular; apply Hτe₁
        apply HNeue₁
      apply Hlc; apply Hlc

theorem preservation𝔹 :
  ∀ size Γ B e₀ e₁, ctx𝔹 B ->
  (∀ τ, typing_strengthened size Γ e₀ τ -> typing_strengthened size Γ e₁ τ) ->
  ∀ τ, typing_strengthened size Γ (B e₀) τ -> typing_strengthened size Γ (B e₁) τ :=
  by
  intro _ _ _ _ _ HB IH _ Hτe₀
  have ⟨HNeue₀, Hτe₀⟩ := Hτe₀
  cases HB with
  | appl₁ =>
    cases Hτe₀ with
    | app₁ _ _ _ _ _ H₀ H₁ =>
      simp at IH
      have ⟨HNeue₁, Hτe₁⟩ := IH _ HNeue₀.left H₀
      constructor
      . constructor; apply HNeue₁; apply HNeue₀.right
      . constructor; apply Hτe₁; apply H₁
  | appr₁ =>
    cases Hτe₀ with
    | app₁ _ _ _ _ _ H₀ H₁ =>
      simp at IH
      have ⟨HNeue₁, Hτe₁⟩ := IH _ HNeue₀.right H₁
      constructor
      . constructor; apply HNeue₀.left; apply HNeue₁
      . constructor; apply H₀; apply Hτe₁
  | appl₂ =>
    cases Hτe₀ with
    | app₂ _ _ _ _ _ H₀ H₁ =>
      simp at IH
      have ⟨HNeue₁, Hτe₁⟩ := IH _ HNeue₀.left H₀
      constructor
      . constructor; apply HNeue₁; apply HNeue₀.right
      . constructor; apply Hτe₁; apply H₁
  | appr₂ =>
    cases Hτe₀ with
    | app₂ _ _ _ _ _ H₀ H₁ =>
      simp at IH
      have ⟨HNeue₁, Hτe₁⟩ := IH _ HNeue₀.right H₁
      constructor
      . constructor; apply HNeue₀.left; apply HNeue₁
      . constructor; apply H₀; apply Hτe₁
  | plusl₁ =>
    cases Hτe₀ with
    | plus₁ _ _ _ H₀ H₁ =>
      simp at IH
      have ⟨HNeue₁, Hτe₁⟩ := IH _ HNeue₀.left H₀
      constructor
      . constructor; apply HNeue₁; apply HNeue₀.right
      . constructor; apply Hτe₁; apply H₁
  | plusr₁ =>
    cases Hτe₀ with
    | plus₁ _ _ _ H₀ H₁ =>
      simp at IH
      have ⟨HNeue₁, Hτe₁⟩ := IH _ HNeue₀.right H₁
      constructor
      . constructor; apply HNeue₀.left; apply HNeue₁
      . constructor; apply H₀; apply Hτe₁
  | plusl₂ =>
    cases Hτe₀ with
    | plus₂ _ _ _ H₀ H₁ =>
      simp at IH
      have ⟨HNeue₁, Hτe₁⟩ := IH _ HNeue₀.left H₀
      constructor
      . constructor; apply HNeue₁; apply HNeue₀.right
      . constructor; apply Hτe₁; apply H₁
  | plusr₂ =>
    cases Hτe₀ with
    | plus₂ _ _ _ H₀ H₁ =>
      simp at IH
      have ⟨HNeue₁, Hτe₁⟩ := IH _ HNeue₀.right H₁
      constructor
      . constructor; apply HNeue₀.left; apply HNeue₁
      . constructor; apply H₀; apply Hτe₁
  | lit₂ =>
    cases Hτe₀ with
    | lit₂ _ _ H =>
      simp at IH
      have ⟨HNeue₁, Hτe₁⟩ := IH _ HNeue₀ H
      constructor
      . apply HNeue₁
      . constructor; apply Hτe₁
  | lam₂ =>
    cases Hτe₀ with
    | lam₂ _ _ _ _ H =>
      simp at IH
      have ⟨HNeue₁, Hτe₁⟩ := IH _ HNeue₀ H
      constructor
      . apply HNeue₁
      . constructor; apply Hτe₁
  | lets =>
    cases Hτe₀ with
    | lets _ _ _ _ _ Hb He Hclose =>
      simp at IH
      have ⟨HNeue₁, Hτe₁⟩ := IH _ HNeue₀.left Hb
      constructor
      . constructor; apply HNeue₁; apply HNeue₀.right
      . constructor; apply Hτe₁; apply He; apply Hclose

theorem preservation_maping_strengthened :
  ∀ size Δ Φ v e τ𝕒 τ𝕓 τ𝕔,
  typing size (Δ ++ τ𝕔 :: Φ) e τ𝕓 ->
  typing size (Δ ++ τ𝕒 :: Φ) v τ𝕔 ->
  typing size (Δ ++ τ𝕒 :: Φ) (subst Φ.length v e) τ𝕓 :=
  by
  intros size Δ Φ v e τ𝕒 τ𝕓 τ𝕔
  generalize HEqΓ : Δ ++ τ𝕔 :: Φ = Γ
  intros Hτe Hτv
  induction Hτe generalizing Δ with
  | fvar _ x _ Hbinds =>
    rw [← HEqΓ] at Hbinds
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      simp; rw [if_neg (Nat.ne_of_lt Hx)]
      constructor
      have Hx : (τ𝕒 :: Φ).length <= x := by simp; omega
      rw [← Nat.add_sub_of_le Hx, Nat.add_comm]
      apply binds_extendr
      apply binds_shrinkr _ (τ𝕔 :: Φ)
      rw [List.length_cons, List.length_cons, Nat.sub_add_cancel]
      apply Hbinds; omega
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      rw [← Hx] at Hbinds
      apply binds_shrink at Hbinds
      simp at Hbinds; rw [← Hbinds]
      simp; rw [if_pos Hx]; apply Hτv; simp
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      simp; rw [if_neg (Nat.ne_of_gt Hx)]
      rw [List.append_cons]
      rw [List.append_cons] at Hbinds
      constructor
      apply binds_extend; apply binds_shrink
      omega; apply Hbinds
  | lam₁ _ _ _ _ _ Hclose IH =>
    rw [← HEqΓ, List.length_append, List.length_cons] at Hclose
    rw [← HEqΓ, subst_open₀_comm, List.length_append, List.length_cons] at IH
    constructor
    rw [← List.cons_append, List.length_append, List.length_cons]
    apply IH; rfl
    apply weakening1; apply Hτv
    apply subst_closed_at
    apply typing_closed; apply Hτv
    rw [List.length_append, List.length_cons]; apply Hclose
    simp; omega
    apply typing_regular; apply Hτv
  | lam𝕔 _ _ _ _ _ Hclose HNeu IH =>
    rw [← HEqΓ, List.length_append, List.length_cons] at Hclose
    rw [← HEqΓ, subst_open₀_comm, List.length_append, List.length_cons] at IH
    constructor
    rw [← List.cons_append, List.length_append, List.length_cons]
    apply IH; rfl
    apply weakening1; apply Hτv
    apply subst_closed_at
    apply typing_closed; apply Hτv
    rw [List.length_append, List.length_cons]; apply Hclose
    apply subst_neutral_db; apply HNeu
    apply typing_regular; apply Hτv
    simp; omega
    apply typing_regular; apply Hτv
  | lets _ _ _ _ _ _ _ Hclose IHb IHe =>
    rw [← HEqΓ, List.length_append, List.length_cons] at Hclose
    rw [← HEqΓ] at IHb
    rw [← HEqΓ, subst_open₀_comm, List.length_append, List.length_cons] at IHe
    constructor
    apply IHb; rfl; apply Hτv
    rw [← List.cons_append, List.length_append, List.length_cons]
    apply IHe; rfl
    apply weakening1; apply Hτv
    apply subst_closed_at
    apply typing_closed; apply Hτv
    rw [List.length_append, List.length_cons]; apply Hclose
    simp; omega
    apply typing_regular; apply Hτv
  | let𝕔 _ _ _ _ _ _ _ Hclose HNeu IHb IHe =>
    rw [← HEqΓ, List.length_append, List.length_cons] at Hclose
    rw [← HEqΓ] at IHb
    rw [← HEqΓ, subst_open₀_comm, List.length_append, List.length_cons] at IHe
    constructor
    apply IHb; rfl; apply Hτv
    rw [← List.cons_append, List.length_append, List.length_cons]
    apply IHe; rfl
    apply weakening1; apply Hτv
    apply subst_closed_at
    apply typing_closed; apply Hτv
    rw [List.length_append, List.length_cons]; apply Hclose
    apply subst_neutral_db; apply HNeu
    apply typing_regular; apply Hτv
    simp; omega
    apply typing_regular; apply Hτv
  | app₁ _ _ _ _ _ _ _ IH₀ IH₁
  | app₂ _ _ _ _ _ _ _ IH₀ IH₁
  | plus₁ _ _ _ _ _ IH₀ IH₁
  | plus₂ _ _ _ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply HEqΓ; apply Hτv
    apply IH₁; apply HEqΓ; apply Hτv
  | code _ _ _ _ IH
  | reflect _ _ _ _ IH
  | lit₂ _ _ _ IH
  | lam₂ _ _ _ _ _ IH =>
    constructor; apply IH; apply HEqΓ; apply Hτv
  | lit₁ => constructor
  | loc _ _ Hsize => constructor; apply Hsize

theorem preservation_maping :
  ∀ size Γ v e τ𝕒 τ𝕓 τ𝕔,
  typing size (τ𝕔 :: Γ) e τ𝕓 ->
  typing size (τ𝕒 :: Γ) v τ𝕔 ->
  typing size (τ𝕒 :: Γ) (subst Γ.length v e) τ𝕓 := by
  intros size Γ v e τ𝕒 τ𝕓 τ𝕔
  rw [← List.nil_append (τ𝕔 :: Γ), ← List.nil_append (τ𝕒 :: Γ)]
  apply preservation_maping_strengthened

theorem preservation_head𝔼 :
  ∀ size Γ E b τ, ctx𝔼 E -> lc b ->
  typing size Γ (E (.reflect b)) τ ->
  typing size Γ (.let𝕔 b (E (.code (.bvar 0)))) τ :=
  by
  intros size Γ E b _ HE Hlc Hτr
  have ⟨_, Hτr, Hτ𝔼⟩ := decompose𝔼 _ _ _ _ _ HE Hτr
  cases Hτr with
  | reflect _ _ τ Hτb =>
    constructor; apply Hτb
    rw [open_ctx𝔼_map _ _ _ HE]; simp
    have Hsubst : .code (.fvar Γ.length) = subst Γ.length (.code (.fvar Γ.length)) (.fvar Γ.length) := by simp
    rw [Hsubst, ← subst𝔼 E (.reflect b)]
    apply preservation_maping; apply Hτ𝔼; repeat constructor; ; simp
    apply HE; apply typing_closed; apply Hτr
    apply closed_at𝔼; apply HE
    apply typing_closed; apply Hτr; constructor
    apply neutral_db𝔼; apply HE
    apply closedb_at_of_neutral_db
    apply typing_regular; apply Hτr; simp

theorem preservation_subst_strengthened :
  ∀ size Γ Δ Φ v e τ𝕒 τ𝕓,
  typing size Γ e τ𝕓 ->
  Γ = Δ ++ τ𝕒 :: Φ ->
  typing size Φ v τ𝕒 ->
  typing size (Δ ++ Φ) (shiftr_at Φ.length (subst Φ.length v e)) τ𝕓 :=
  by
  intros size Γ Δ Φ v e τ𝕒 τ𝕓 Hτe HEqΓ Hτv
  induction Hτe generalizing Δ with
  | fvar _ x _ Hbinds =>
    rw [HEqΓ] at Hbinds
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      simp; rw [if_neg (Nat.ne_of_lt Hx)]
      simp; rw [if_pos Hx]
      constructor
      have Hx : Φ.length <= x - 1 := by omega
      rw [← Nat.add_sub_of_le Hx, Nat.add_comm]
      apply binds_extendr
      rw [← Nat.sub_add_eq, Nat.add_comm]
      apply binds_shrinkr _ (τ𝕒 :: Φ)
      rw [List.length_cons, Nat.sub_add_cancel]
      apply Hbinds; omega
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      rw [← Hx] at Hbinds
      apply binds_shrink at Hbinds
      simp at Hbinds; rw [← Hbinds]
      simp; rw [if_pos Hx]
      rw [shiftr_id]
      apply weakening; apply Hτv
      apply closed_inc; apply typing_closed
      apply Hτv; omega
      simp
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      simp; rw [if_neg (Nat.ne_of_gt Hx)]
      simp; rw [if_neg (Nat.not_lt_of_gt Hx)]
      constructor
      apply binds_extend; apply binds_shrink
      omega; rw [List.append_cons] at Hbinds; apply Hbinds
  | lam₁ _ _ _ _ _ Hclose IH =>
    rw [HEqΓ] at IH; rw [HEqΓ] at Hclose
    rw [subst_open₀_comm, shiftr_open₀] at IH
    simp at IH
    constructor
    simp; rw [← List.cons_append]; apply IH; rfl
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
  | lam𝕔 _ _ _ _ _ Hclose HNeu IH =>
    rw [HEqΓ] at IH; rw [HEqΓ] at Hclose
    rw [subst_open₀_comm, shiftr_open₀] at IH
    simp at IH
    constructor
    simp; rw [← List.cons_append]; apply IH; rfl
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
    apply shiftr_neutral_db
    apply subst_neutral_db; apply HNeu
    apply typing_regular; apply Hτv
    simp; omega
    simp; omega
    apply typing_regular; apply Hτv
  | lets _ _ _ _ _ _ _ Hclose IHb IHe =>
    rw [HEqΓ] at IHb; rw [HEqΓ] at IHe; rw [HEqΓ] at Hclose
    rw [subst_open₀_comm, shiftr_open₀] at IHe
    simp at IHb; simp at IHe
    constructor
    apply IHb
    simp; rw [← List.cons_append]; apply IHe; rfl
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
  | let𝕔 _ _ _ _ _ _ _ Hclose HNeu IHb IHe =>
    rw [HEqΓ] at IHb; rw [HEqΓ] at IHe; rw [HEqΓ] at Hclose
    rw [subst_open₀_comm, shiftr_open₀] at IHe
    simp at IHb; simp at IHe
    constructor
    apply IHb
    simp; rw [← List.cons_append]; apply IHe; rfl
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
    apply shiftr_neutral_db
    apply subst_neutral_db; apply HNeu
    apply typing_regular; apply Hτv
    simp; omega
    simp; omega
    apply typing_regular; apply Hτv
  | app₁ _ _ _ _ _ _ _ IH₀ IH₁
  | app₂ _ _ _ _ _ _ _ IH₀ IH₁
  | plus₁ _ _ _ _ _ IH₀ IH₁
  | plus₂ _ _ _ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply HEqΓ
    apply IH₁; apply HEqΓ
  | code _ _ _ _ IH
  | reflect _ _ _ _ IH
  | lit₂ _ _ _ IH
  | lam₂ _ _ _ _ _ IH =>
    constructor; apply IH; apply HEqΓ
  | lit₁ => constructor
  | loc _ _ Hsize => constructor; apply Hsize

theorem preservation_subst :
    ∀ size Γ v e τ𝕒 τ𝕓, typing size Γ v τ𝕒 -> typing size (τ𝕒 :: Γ) e τ𝕓 -> typing size Γ (subst Γ.length v e) τ𝕓 :=
  by
  intros size Γ v e τ𝕒 τ𝕓 Hτv Hτe
  have H := preservation_subst_strengthened size (τ𝕒 :: Γ) [] Γ v e τ𝕒 τ𝕓
  simp at H
  have H := H Hτe Hτv
  rw [shiftr_id] at H
  apply H
  apply subst_closed_at
  apply closed_inc; apply typing_closed; apply Hτv; omega
  rw [← List.length_cons]; apply typing_closed; apply Hτe

theorem preservation_swap_strengthened :
  ∀ size Γ Δ Φ e τ𝕒₀ τ𝕒₁ τ𝕓,
  typing size Γ e τ𝕓 ->
  Γ = Δ ++ τ𝕒₀ :: τ𝕒₁ :: Φ ->
  typing size (Δ ++ τ𝕒₁ :: τ𝕒₀ :: Φ) (swap (Φ.length + 1) Φ.length e) τ𝕓 :=
  by
  intros size Γ Δ Φ e τ𝕒₀ τ𝕒₁ τ𝕓 Hτ HEqΓ
  induction Hτ generalizing Δ with
  | fvar _ x _ Hbinds =>
    rw [HEqΓ] at Hbinds
    simp; by_cases HEqΦ : x = Φ.length
    . rw [HEqΦ]; rw [HEqΦ] at Hbinds
      simp; constructor
      apply binds_shrink at Hbinds
      apply binds_extend
      simp at *; apply Hbinds
      simp; omega
    . rw [if_neg HEqΦ]
      by_cases HEqΦ₁ : x = Φ.length + 1
      . rw [HEqΦ₁]; rw [HEqΦ₁] at Hbinds
        simp; constructor
        apply binds_shrink at Hbinds
        apply binds_extend
        simp at *; apply Hbinds
        simp
      . rw [if_neg HEqΦ₁]; by_cases HLe : Φ.length + 1 + 1 <= x
        . constructor
          repeat rw [← List.length_cons] at HLe
          rw [← Nat.add_sub_of_le HLe, Nat.add_comm]
          apply binds_extendr
          apply binds_shrinkr _ (τ𝕒₀ :: τ𝕒₁ :: Φ)
          simp; rw [Nat.sub_add_cancel]; apply Hbinds
          simp at HLe; omega
        . constructor
          apply binds_shrink at Hbinds
          apply binds_extend
          simp at Hbinds; rw [if_neg (ne_comm.mp HEqΦ), if_neg (ne_comm.mp HEqΦ₁)] at Hbinds
          simp; rw [if_neg (ne_comm.mp HEqΦ), if_neg (ne_comm.mp HEqΦ₁)]
          apply Hbinds
          simp; omega
  | lam₁ _ _ _ _ _ Hclose IH =>
    rw [HEqΓ] at IH Hclose
    rw [List.length_append, List.length_cons, List.length_cons] at IH
    constructor
    rw [open₀_swap_comm, ← List.cons_append]
    rw [List.length_append, List.length_cons, List.length_cons]
    apply IH; rfl
    simp; omega
    simp; omega
    apply swap_closed
    simp; omega
    simp; omega
    simp at *; apply Hclose
  | lam𝕔 _ _ _ _ _ Hclose HNeu IH =>
    rw [HEqΓ] at IH Hclose
    rw [List.length_append, List.length_cons, List.length_cons] at IH
    constructor
    rw [open₀_swap_comm, ← List.cons_append]
    rw [List.length_append, List.length_cons, List.length_cons]
    apply IH; rfl
    simp; omega
    simp; omega
    apply swap_closed
    simp; omega
    simp; omega
    simp at *; apply Hclose
    apply swap_neutraldb; apply HNeu
  | lets _ _ _ _ _ _ _ Hclose IHb IHe =>
    rw [HEqΓ] at IHb IHe Hclose
    rw [List.length_append, List.length_cons, List.length_cons] at IHe
    constructor
    apply IHb; rfl
    rw [open₀_swap_comm, ← List.cons_append]
    rw [List.length_append, List.length_cons, List.length_cons]
    apply IHe; rfl
    simp; omega
    simp; omega
    apply swap_closed
    simp; omega
    simp; omega
    simp at *; apply Hclose
  | let𝕔 _ _ _ _ _ _ _ Hclose HNeu IHb IHe =>
    rw [HEqΓ] at IHb IHe Hclose
    rw [List.length_append, List.length_cons, List.length_cons] at IHe
    constructor
    apply IHb; rfl
    rw [open₀_swap_comm, ← List.cons_append]
    rw [List.length_append, List.length_cons, List.length_cons]
    apply IHe; rfl
    simp; omega
    simp; omega
    apply swap_closed
    simp; omega
    simp; omega
    simp at *; apply Hclose
    apply swap_neutraldb; apply HNeu
  | app₁ _ _ _ _ _ _ _ IH₀ IH₁
  | app₂ _ _ _ _ _ _ _ IH₀ IH₁
  | plus₁ _ _ _ _ _ IH₀ IH₁
  | plus₂ _ _ _ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply HEqΓ
    apply IH₁; apply HEqΓ
  | code _ _ _ _ IH
  | reflect _ _ _ _ IH
  | lit₂ _ _ _ IH
  | lam₂ _ _ _ _ _ IH =>
    constructor; apply IH; apply HEqΓ
  | lit₁ => constructor
  | loc _ _ Hsize => constructor; apply Hsize

theorem preservation_swap :
  ∀ size Γ e τ𝕒₀ τ𝕒₁ τ𝕓,
  typing size (τ𝕒₀ :: τ𝕒₁ :: Γ) e τ𝕓 ->
  typing size (τ𝕒₁ :: τ𝕒₀ :: Γ) (swap (Γ.length + 1) Γ.length e) τ𝕓 :=
  by
  intros size Γ e τ𝕒₀ τ𝕒₁ τ𝕓 Hτ
  rw [← List.nil_append (τ𝕒₁ :: τ𝕒₀ :: Γ)]
  apply preservation_swap_strengthened
  apply Hτ; simp

theorem neutral_head𝕄 : ∀ x e₀ e₁, head𝕄 e₀ e₁ -> neutral x e₀ -> neutral x e₁ :=
  by
  intros x e₀ e₁ Hhead HNeu
  cases Hhead with
  | lets =>
    apply neutral_opening
    apply HNeu.right; apply HNeu.left
  | app₁ =>
    apply neutral_opening
    apply HNeu.left; apply HNeu.right
  | app₂| plus₂| lit₂| lam𝕔| let𝕔₀ => apply HNeu
  | plus₁| let𝕔₁| let𝕔₃ => simp
  | lam₂ =>
    apply maping𝕔_neutral; apply HNeu
  | let𝕔₂ =>
    constructor
    apply HNeu.left
    apply swapdb_neutral; apply HNeu.right

theorem preservation_head𝕄 : ∀ size Γ e₀ e₁ τ, head𝕄 e₀ e₁ -> lc e₀ -> typing size Γ e₀ τ -> typing size Γ e₁ τ :=
  by
  intros size Γ e₀ e₁ τ Hhead Hlc Hτ
  cases Hhead with
  | lets =>
    cases Hτ
    next Hτv Hclose Hτe =>
      simp; rw [← subst_intro]
      apply preservation_subst
      apply Hτv; apply Hτe; apply Hclose
  | app₁ =>
    cases Hτ
    next Hτv Hτf =>
      cases Hτf
      next Hclose Hτe =>
        simp; rw [← subst_intro]
        apply preservation_subst
        apply Hτv; apply Hτe; apply Hclose
  | app₂ =>
    cases Hτ
    next Hτf𝕔 Hτarg𝕔 =>
      cases Hτf𝕔
      next Hτf =>
        cases Hτarg𝕔
        next Hτarg =>
          repeat constructor
          apply Hτf; apply Hτarg
  | plus₁ => cases Hτ; constructor
  | plus₂ =>
    cases Hτ
    next Hl𝕔 Hr𝕔 =>
      cases Hl𝕔
      next Hl =>
        cases Hr𝕔
        next Hr =>
          repeat constructor
          apply Hl; apply Hr
  | lit₂ => cases Hτ; repeat constructor
  | lam₂ =>
    cases Hτ
    next Hτ =>
      cases Hτ
      next Hclose Hτe =>
        rw [← map𝕔₀_intro]
        constructor
        simp; rw [open_close_id]
        apply preservation_maping; apply Hτe; repeat constructor; ; simp
        apply subst_closedb_at; simp; apply open_closedb'; apply Hlc
        apply close_closed; apply subst_closed_at; simp; apply open_closed; apply Hclose
        rw [map𝕔₀_intro]; apply maping𝕔_neutral_db; apply Hclose
        apply Hclose
  | lam𝕔 =>
    cases Hτ
    next Hτe𝕔 _ =>
      cases Hτe𝕔
      next Hclose Hτe =>
        repeat constructor
        apply Hτe; apply Hclose
  | let𝕔₀ =>
    cases Hτ
    next Hτv _ Hclose Hτe𝕔 =>
      cases Hτe𝕔
      next Hτe =>
        repeat constructor
        apply Hτv; apply Hτe; apply Hclose
  | let𝕔₁ =>
    cases Hτ
    next Hτ =>
      cases Hτ
      constructor
  | let𝕔₂ =>
    cases Hτ with
    | let𝕔 _ _ _ _ _ Hτb Hτe Hclose HNeu =>
      cases Hτe with
      | lam₁ _ _ _ _ Hτe =>
        constructor
        constructor
        rw [closedb_opening_id]; apply weakening1; apply Hτb
        apply Hlc.left
        simp; rw [open_swapdb_comm]
        apply preservation_swap; apply Hτe
        apply closed_inc; apply Hclose; omega
        apply Hclose
        omega
        apply open_closed; apply swapdb_closed; apply Hclose
        apply opening_neutral_db; apply swapdb_neutral_db; apply HNeu
        constructor
        apply typing_closed; apply Hτb
        apply swapdb_closed; apply Hclose
  | let𝕔₃ =>
    cases Hτ
    next Hτ =>
      cases Hτ
      next Hsize =>
      constructor; apply Hsize

theorem preservation_strengthened : ∀ Γ st₀ st₁ e₀ e₁ τ, step_lvl Γ.length (st₀, e₀) (st₁, e₁) -> typing_strengthened st₀.length Γ e₀ τ -> typing_strengthened st₁.length Γ e₁ τ :=
  by
  intro Γ st₀ st₁ e₀ e₁ τ
  generalize HEqlvl : Γ.length = lvl
  intro Hstep Hτ; cases Hstep with
  | step𝕄 _ _ _ _ HM Hlc Hhead𝕄 =>
    induction HM generalizing τ Γ with
    | hole =>
      constructor
      . apply neutral_head𝕄; apply Hhead𝕄; apply Hτ.left
      . apply preservation_head𝕄; apply Hhead𝕄; apply Hlc; apply Hτ.right
    | cons𝔹 _ _ HB _ IHM =>
      simp; apply preservation𝔹
      apply HB; intro; apply IHM
      apply HEqlvl; apply Hτ
    | consℝ _ _ HR HM IHM =>
      rw [← HEqlvl] at HR IHM; simp; apply preservationℝ
      apply HR
      apply lc_ctx𝕄; apply HM; apply Hlc
      intros _ _; apply IHM; rfl
      apply Hτ
  | reflect P E e _ HP HE Hlc =>
    generalize HPQ : ℙℚ.ℙ = PQ
    simp at HP; rw [HPQ] at HP
    clear HPQ
    induction HP generalizing τ Γ with
    | hole =>
      constructor
      . constructor
        . apply closed_at_decompose𝔼 _ _ _ HE (typing_closed _ _ _ _ Hτ.right)
        . apply neutral𝔼; apply HE; apply Hτ.left; simp
      . apply preservation_head𝔼; apply HE; apply Hlc; apply Hτ.right
    | cons𝔹 _ _ HB _ IHM =>
      simp; apply preservation𝔹
      apply HB; intro; apply IHM
      apply HEqlvl; apply Hτ
    | consℝ _ _ HR HP IHM =>
      rw [← HEqlvl] at HR IHM; simp; apply preservationℝ
      apply HR
      apply lc_ctxℙ; apply HP
      apply lc_ctx𝔼 _ (.reflect e); apply HE; apply Hlc
      intros _ _; apply IHM; rfl
      apply Hτ

theorem preservation : ∀ st₀ st₁ e₀ e₁ τ, step (st₀, e₀) (st₁, e₁) -> typing st₀.length [] e₀ τ -> typing st₁.length [] e₁ τ :=
  by
  intros st₀ st₁ e₀ e₁ τ Hstep Hτ
  apply And.right; apply preservation_strengthened
  apply Hstep; apply typing_weakening_empty; apply Hτ
