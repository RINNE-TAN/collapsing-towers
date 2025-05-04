
import CollapsingTowers.TwoLevel.Basic
import CollapsingTowers.TwoLevel.SmallStep
import CollapsingTowers.TwoLevel.Typing
theorem typing𝔹 : ∀ Γ B e τ, ctx𝔹 B -> typing Γ (B e) τ -> ∃ τ, typing Γ e τ :=
  by
  intros Γ B e τ HB
  cases HB
  all_goals
    intro Hτ; cases Hτ
    next H₀ H₁ H₂ =>
      constructor
      first
      | apply H₀
      | apply H₁
      | apply H₂

theorem typing𝔼 : ∀ Γ E e τ, ctx𝔼 E -> typing Γ (E e) τ -> ∃ τ, typing Γ e τ :=
  by
  intros _ _ _ τ HE
  induction HE generalizing τ with
  | hole => intro; exists τ
  | cons𝔹 _ _ HB HE IH =>
    intro Hτ
    have ⟨τ, Hτ⟩ := typing𝔹 _ _ _ _ HB Hτ
    apply IH; apply Hτ

theorem preservationℝ :
    ∀ Γ R e₀ e₁,
      ctxℝ Γ.length R ->
        lc e₀ ->
          (∀ τ𝕒 τ𝕓, typing (τ𝕒 :: Γ) e₀ τ𝕓 -> typing (τ𝕒 :: Γ) e₁ τ𝕓) -> ∀ τ, typing Γ (R e₀) τ -> typing Γ (R e₁) τ :=
  by
  intro Γ _ e₀ e₁ HR Hlc HτMap _ Hτe₀
  cases HR with
  | lam𝕔 =>
    cases Hτe₀ with
    | lam𝕔 _ _ _ _ Hτe₀ =>
      have Hopen_close_e₀ := open_close_id₀ e₀ Γ.length Hlc
      rw [Hopen_close_e₀] at Hτe₀
      have Hτe₁ := HτMap _ _ Hτe₀
      have Hopen_close_e₀ := open_close_id₀ e₁ Γ.length (typing_regular _ _ _ Hτe₁)
      constructor
      rw [Hopen_close_e₀]
      apply Hτe₁
      apply close_closed
      apply typing_closed _ _ _ Hτe₁
  | let𝕔 =>
    cases Hτe₀ with
    | let𝕔 _ _ _ _ _ Hτb Hτe₀ =>
      have Hopen_close_e₀ := open_close_id₀ e₀ Γ.length Hlc
      rw [Hopen_close_e₀] at Hτe₀
      have Hτe₁ := HτMap _ _ Hτe₀
      have Hopen_close_e₀ := open_close_id₀ e₁ Γ.length (typing_regular _ _ _ Hτe₁)
      constructor
      apply Hτb
      rw [Hopen_close_e₀]
      apply Hτe₁
      apply close_closed
      apply typing_closed _ _ _ Hτe₁

theorem preservation𝔹 :
    ∀ Γ B e₀ e₁, ctx𝔹 B -> (∀ τ, typing Γ e₀ τ -> typing Γ e₁ τ) -> ∀ τ, typing Γ (B e₀) τ -> typing Γ (B e₁) τ :=
  by
  intro _ _ _ _ HB HτMap _ Hτe₀
  cases HB
  all_goals
    cases Hτe₀
    next H₀ H₁ H₂ =>
      constructor
      repeat
        first
        | apply HτMap
        | apply H₀
        | apply H₁
        | apply H₂

theorem preservation𝔼 :
    ∀ Γ E e₀ e₁, ctx𝔼 E -> (∀ τ, typing Γ e₀ τ -> typing Γ e₁ τ) -> ∀ τ, typing Γ (E e₀) τ -> typing Γ (E e₁) τ :=
  by
  intro _ _ _ _ HE HτMap τ Hτe₀
  induction HE generalizing τ with
  | hole => apply HτMap; apply Hτe₀
  | cons𝔹 _ _ HB _ IHM =>
    simp; apply preservation𝔹
    apply HB
    intro _; apply IHM; apply Hτe₀

theorem preservation_reflect :
    ∀ Γ b τ𝕒 τ𝕓,
      typing (τ𝕒 :: Γ) b τ𝕒 -> typing (τ𝕒 :: Γ) (.reflect b) τ𝕓 -> typing (τ𝕒 :: Γ) (.code (.fvar Γ.length)) τ𝕓 :=
  by
  intros Γ b τ𝕒 τ𝕓 Hτb Hτr
  cases Hτr with
  | reflect _ _ _ Hτrb =>
    constructor
    constructor
    simp
    apply typing_unique; apply Hτb; apply Hτrb

theorem preservation_head𝔼 :
    ∀ Γ E b τ, ctx𝔼 E -> lc b -> typing Γ (E (.reflect b)) τ -> typing Γ (.let𝕔 b (E (.code (.bvar 0)))) τ :=
  by
  intros _ _ _ _ HE Hlc Hτr
  have ⟨_, Hτr⟩ := typing𝔼 _ _ _ _ HE Hτr
  cases Hτr with
  | reflect _ _ τ Hτb =>
    constructor
    apply Hτb
    rw [open_ctx𝔼_map _ _ _ HE]
    apply preservation𝔼; apply HE
    intro; apply preservation_reflect
    rw [← List.singleton_append]; apply typing_extend; apply Hτb
    rw [← List.singleton_append]; apply typing_extend; apply Hτr
    apply close_at𝔼; apply HE
    apply typing_closed; apply Hτr; constructor

theorem preservation_maping :
    ∀ Γ v e τ𝕒 τ𝕓 τ𝕔, typing (τ𝕔 :: Γ) e τ𝕓 -> typing (τ𝕒 :: Γ) v τ𝕔 -> typing (τ𝕒 :: Γ) (subst Γ.length v e) τ𝕓 := by
  admit

theorem preservation_opening :
    ∀ Γ v₀ v₁ i e τ𝕒 τ𝕓,
      typing Γ v₀ τ𝕒 -> typing Γ v₁ τ𝕒 -> typing Γ (opening i v₀ e) τ𝕓 -> typing Γ (opening i v₁ e) τ𝕓 :=
  by admit

theorem preservation_subst :
    ∀ Γ v e τ𝕒 τ𝕓, typing Γ v τ𝕒 -> typing (τ𝕒 :: Γ) e τ𝕓 -> typing Γ (subst Γ.length v e) τ𝕓 :=
  by
  intros Γ v e τ𝕒 τ𝕓 Hv
  generalize EqΓ : τ𝕒 :: Γ = Δ
  intro He
  induction He generalizing Γ τ𝕒 with
  | fvar _ x _ Hbind =>
    rw [← EqΓ] at Hbind
    simp at Hbind
    by_cases HEq : Γ.length = x
    . rw [HEq]; rw [HEq] at Hbind; simp at *; rw [← Hbind]; apply Hv
    . simp; rw [if_neg HEq]; rw [if_neg HEq] at Hbind; constructor; apply Hbind
  | lam₁ =>
    constructor
    admit
    admit
  | app₁ _ _ _ _ _ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hv; apply EqΓ
    apply IH₁; apply Hv; apply EqΓ
  | _ => admit

theorem preservation_head𝕄 : ∀ Γ e₀ e₁ τ, head𝕄 e₀ e₁ -> lc e₀ -> typing Γ e₀ τ -> typing Γ e₁ τ :=
  by
  intros Γ e₀ e₁ τ Hhead Hlc Hτ
  induction Hhead with
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
    next Hclose Hτe =>
      rw [← map𝕔₀_intro]
      constructor
      simp; rw [open_close_id]
      apply preservation_maping; apply Hτe; repeat constructor; ; simp
      apply subst_closedb_at; simp; apply open_closedb'; apply Hlc
      apply close_closed; apply subst_closed_at; simp; apply open_closed; apply Hclose
      apply Hclose
  | lam𝕔 =>
    cases Hτ
    next Hτe𝕔 =>
      cases Hτe𝕔
      next Hclose Hτe =>
        repeat constructor
        apply Hτe; apply Hclose
  | let𝕔 =>
    cases Hτ
    next Hτv Hclose Hτe𝕔 =>
      cases Hτe𝕔
      next Hτe =>
        repeat constructor
        apply Hτv; apply Hτe; apply Hclose

theorem preservation : ∀ e₀ e₁ τ, step e₀ e₁ -> typing [] e₀ τ -> typing [] e₁ τ :=
  by
  intro e₀ e₁ τ Hstep
  cases Hstep with
  | step𝕄 _ _ _ HM Hlc Hhead𝕄 =>
    generalize HeqΓ : [] = Γ
    generalize HEqlvl : 0 = lvl
    have Hlength : Γ.length = lvl := by
      rw [← HeqΓ, ← HEqlvl]
      simp
    rw [HEqlvl] at HM
    clear HEqlvl
    clear HeqΓ
    induction HM generalizing τ Γ with
    | hole => apply preservation_head𝕄; apply Hhead𝕄; apply Hlc
    | cons𝔹 _ _ HB _ IHM =>
      simp; apply preservation𝔹
      apply HB
      intro; apply IHM; apply Hlength
    | consℝ _ _ HR HM IHM =>
      rw [← Hlength] at HR IHM; simp; apply preservationℝ
      apply HR
      apply lc_ctx𝕄; apply HM; apply Hlc
      intros _ _; apply IHM; rfl
  | reflect P E e HP HE Hlc =>
    generalize HeqΓ : [] = Γ
    generalize HEqlvl : 0 = lvl
    have Hlength : Γ.length = lvl := by
      rw [← HeqΓ, ← HEqlvl]
      simp
    rw [← HEqlvl]
    rw [HEqlvl] at HP
    clear HEqlvl
    clear HeqΓ
    induction HP generalizing τ Γ with
    | hole => apply preservation_head𝔼; apply HE; apply Hlc
    | holeℝ _ HR =>
      apply preservationℝ
      rw [Hlength]; apply HR
      apply lc_ctx𝔼; apply HE; apply Hlc
      intros _ _; apply preservation_head𝔼; apply HE; apply Hlc
    | cons𝔹 _ _ HB _ IHM =>
      simp; apply preservation𝔹
      apply HB
      intro; apply IHM; apply Hlength
    | consℝ _ _ HR HP IHM =>
      rw [← Hlength] at HR IHM; simp; apply preservationℝ
      apply HR
      apply lc_ctxℙ; apply HP
      apply lc_ctx𝔼; apply HE; apply Hlc
      intros _ _; apply IHM; rfl
