
import CollapsingTowers.TwoLevelPCP.Typing
@[simp]
def dyn_env (Γ : TEnv) : Prop :=
  ∀ x τ 𝕊, binds x (τ, 𝕊) Γ → ¬𝕊 = .stat

theorem dyn_env_extend :
  ∀ Γ τ,
    dyn_env Γ →
    dyn_env ((τ, .dyn) :: Γ) :=
  by
  intros Γ τ₀ HDyn x τ₁ 𝕊 Hbinds HEq𝕊
  simp at Hbinds; rw [HEq𝕊] at Hbinds
  by_cases HEqx : (Γ.length = x)
  . rw [if_pos HEqx] at Hbinds
    nomatch Hbinds
  . rw [if_neg HEqx] at Hbinds
    apply HDyn; apply Hbinds; rfl

theorem progress_strengthened :
  ∀ Γ σ st₀ e₀ τ φ,
    well_store σ st₀ →
    typing_reification Γ σ e₀ τ φ →
    dyn_env Γ →
    value e₀ ∨ ∃ st₁ e₁, step_lvl Γ.length (st₀, e₀) (st₁, e₁) :=
  by
  intros Γ σ st₀ e₀ τ φ HwellStore Hτ
  revert HwellStore
  apply @typing_reification.rec
    (fun Γ σ 𝕊 e₀ τ φ (H : typing Γ σ 𝕊 e₀ τ φ) =>
      well_store σ st₀ →
      dyn_env Γ →
      𝕊 = .stat →
      value e₀ ∨ ∃ st₁ e₁, step_lvl Γ.length (st₀, e₀) (st₁, e₁))
    (fun Γ σ e₀ τ φ (H : typing_reification Γ σ e₀ τ φ) =>
      well_store σ st₀ →
      dyn_env Γ →
      value e₀ ∨ ∃ st₁ e₁, step_lvl Γ.length (st₀, e₀) (st₁, e₁))
  case fvar =>
    intros _ _ _ x _ Hbinds HwellBinds HwellStore HDyn HEq𝕊
    exfalso; apply HDyn; apply Hbinds; apply HEq𝕊
  case lam₁ =>
    intros _ _ _ _ _ _ _ H HwellBinds Hclose IH HwellStore HDyn HEq𝕊
    left; constructor
    apply (open_closedb _ _ _).mp; apply typing_regular; apply H
  case lift_lam =>
    intros _ _ _ _ _ _ _ H IH HwellStore HDyn HEq𝕊
    right
    cases IH HwellStore HDyn rfl with
    | inl Hvalue =>
      cases Hvalue with
      | lam₁ e Hlc =>
        exists st₀, .lam𝕔 (map𝕔₀ e)
        apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
        apply Hlc; apply head𝕄.lift_lam
      | _ => nomatch H
    | inr Hstep =>
      have ⟨st₁, _, Hstep⟩ := Hstep; exists st₁
      apply step𝔹 _ _ _ _ _ _ ctx𝔹.lift; apply Hstep
  case app₁ =>
    intros _ _ _ e₀ e₁ _ _ _ _ _ H₀ H₁ IH₀ IH₁ HwellStore HDyn HEq𝕊
    right
    cases IH₀ HwellStore HDyn HEq𝕊 with
    | inl Hvalue₀ =>
      cases IH₁ HwellStore HDyn HEq𝕊 with
      | inl Hvalue₁ =>
        cases Hvalue₀ with
        | lam₁ e₀ Hlc₀ =>
          exists st₀, open_subst e₁ e₀
          apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
          constructor; apply Hlc₀; apply value_lc; apply Hvalue₁
          apply head𝕄.app₁; apply Hvalue₁
        | _ => nomatch H₀
      | inr Hstep₁ =>
        have ⟨st₁, _, Hstep₁⟩ := Hstep₁; exists st₁
        apply step𝔹 _ _ _ _ _ _ (ctx𝔹.appr₁ _ _); apply Hstep₁
        apply Hvalue₀
    | inr Hstep₀ =>
      have ⟨st₁,_, Hstep₀⟩ := Hstep₀; exists st₁
      apply step𝔹 _ _ _ _ _ _ (ctx𝔹.appl₁ _ _); apply Hstep₀
      apply typing_regular; apply H₁
  case app₂ =>
    intros _ _ e₀ e₁ _ _ _ _ H₀ H₁ IH₀ IH₁ HwellStore HDyn HEq𝕊
    right
    cases IH₀ HwellStore HDyn HEq𝕊 with
    | inl Hvalue₀ =>
      cases IH₁ HwellStore HDyn HEq𝕊 with
      | inl Hvalue₁ =>
        cases Hvalue₀ with
        | code e₀ Hlc₀ =>
          cases Hvalue₁ with
          | code e₁ Hlc₁ =>
            exists st₀, .reflect (.app₁ e₀ e₁)
            apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
            constructor; apply Hlc₀; apply Hlc₁
            apply head𝕄.app₂
          | _ => nomatch H₁
        | _ => nomatch H₀
      | inr Hstep₁ =>
        have ⟨st₁, _, Hstep₁⟩ := Hstep₁; exists st₁
        apply step𝔹 _ _ _ _ _ _ (ctx𝔹.appr₂ _ _); apply Hstep₁
        apply Hvalue₀
    | inr Hstep₀ =>
      have ⟨st₁, _, Hstep₀⟩ := Hstep₀; exists st₁
      apply step𝔹 _ _ _ _ _ _ (ctx𝔹.appl₂ _ _); apply Hstep₀
      apply typing_regular; apply H₁
  case plus₁ =>
    intros _ _ _ e₀ e₁ _ _ H₀ H₁ IH₀ IH₁ HwellStore HDyn HEq𝕊
    right
    cases IH₀ HwellStore HDyn HEq𝕊 with
    | inl Hvalue₀ =>
      cases IH₁ HwellStore HDyn HEq𝕊 with
      | inl Hvalue₁ =>
        cases Hvalue₀ with
        | lit₁ e₀ =>
          cases Hvalue₁ with
          | lit₁ e₁ =>
            exists st₀, .lit₁ (e₀ + e₁)
            apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
            simp; apply head𝕄.plus₁
          | _ => nomatch H₁
        | _ => nomatch H₀
      | inr Hstep₁ =>
        have ⟨st₁, _, Hstep₁⟩ := Hstep₁; exists st₁
        apply step𝔹 _ _ _ _ _ _ (ctx𝔹.plusr₁ _ _); apply Hstep₁
        apply Hvalue₀
    | inr Hstep₀ =>
      have ⟨st₁, _, Hstep₀⟩ := Hstep₀; exists st₁
      apply step𝔹 _ _ _ _ _ _ (ctx𝔹.plusl₁ _ _); apply Hstep₀
      apply typing_regular; apply H₁
  case plus₂ =>
    intros _ _ e₀ e₁ _ _ H₀ H₁ IH₀ IH₁ HwellStore HDyn HEq𝕊
    right
    cases IH₀ HwellStore HDyn HEq𝕊 with
    | inl Hvalue₀ =>
      cases IH₁ HwellStore HDyn HEq𝕊 with
      | inl Hvalue₁ =>
        cases Hvalue₀ with
        | code e₀ Hlc₀ =>
          cases Hvalue₁ with
          | code e₁ Hlc₁ =>
            exists st₀, .reflect (.plus₁ e₀ e₁)
            apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
            constructor; apply Hlc₀; apply Hlc₁
            apply head𝕄.plus₂
          | _ => nomatch H₁
        | _ => nomatch H₀
      | inr Hstep₁ =>
        have ⟨st₁, _, Hstep₁⟩ := Hstep₁; exists st₁
        apply step𝔹 _ _ _ _ _ _ (ctx𝔹.plusr₂ _ _); apply Hstep₁
        apply Hvalue₀
    | inr Hstep₀ =>
      have ⟨st₁, _, Hstep₀⟩ := Hstep₀; exists st₁
      apply step𝔹 _ _ _ _ _ _ (ctx𝔹.plusl₂ _ _); apply Hstep₀
      apply typing_regular; apply H₁
  case lit₁ => intros; left; constructor
  case lift_lit =>
    intros _ _ _ _ H IH HwellStore HDyn HEq𝕊
    right
    cases IH HwellStore HDyn HEq𝕊 with
    | inl Hvalue =>
      cases Hvalue with
      | lit₁ e =>
        exists st₀, .reflect (.lit₁ e)
        apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
        simp; apply head𝕄.lift_lit
      | _ => nomatch H
    | inr Hstep =>
      have ⟨st₁, _, Hstep⟩ := Hstep; exists st₁
      apply step𝔹 _ _ _ _ _ _ ctx𝔹.lift; apply Hstep
  case code_fragment => intros; left; constructor; simp
  case code_rep =>
    intros _ _ _ _ H IH HwellStore HDyn HEq𝕊
    left; constructor
    apply typing_regular; apply H
  case reflect =>
    intros _ _ e _ H _ _ _ _
    right; exists st₀, .let𝕔 e (.code (.bvar 0))
    apply step_lvl.reflect _ _ _ _ ctxℙ.hole ctx𝔼.hole
    apply typing_regular; apply H
  case lam𝕔 =>
    intros Γ _ e _ _ _ H HwellBinds Hclose IH HwellStore HDyn HEq𝕊
    right
    rw [← close_open_id₀ e _ Hclose]
    cases IH HwellStore (dyn_env_extend _ _ HDyn) with
    | inl Hvalue =>
      generalize HEqe : open₀ Γ.length e = e𝕠
      rw [HEqe] at Hvalue H
      cases Hvalue with
      | code e Hlc =>
        exists st₀, .reflect (.lam₁ (close₀ Γ.length e))
        apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
        apply close_closedb; omega
        apply closedb_inc; apply Hlc; omega
        apply head𝕄.lam𝕔
      | _ => contradiction
    | inr Hstep =>
      have ⟨st₁, _, Hstep⟩ := Hstep; exists st₁
      constructor
      apply stepℝ _ _ _ _ _ _ _ ctxℝ.lam𝕔; apply Hstep
  case lets =>
    intros _ _ _ e₀ e₁ _ _ _ _ H₀ H₁ _ _ IH₀ IH₁ HwellStore HDyn HEq𝕊
    right
    cases IH₀ HwellStore HDyn HEq𝕊 with
    | inl Hvalue₀ =>
      exists st₀, open_subst e₀ e₁
      apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
      constructor
      apply value_lc; apply Hvalue₀
      apply (open_closedb _ _ _).mp; apply typing_regular; apply H₁
      apply head𝕄.lets; apply Hvalue₀
    | inr Hstep₀ =>
      have ⟨st₁, _, Hstep₀⟩ := Hstep₀; exists st₁
      apply step𝔹 _ _ _ _ _ _ (ctx𝔹.lets _ _); apply Hstep₀
      apply (open_closedb _ _ _).mp; apply typing_regular; apply H₁
  case let𝕔 =>
    intros Γ _ b e _ _ _ H₀ H₁ HwellBinds Hclose _ IH₁ HwellStore HDyn HEq𝕊
    right
    rw [← close_open_id₀ e _ Hclose]
    cases IH₁ HwellStore (dyn_env_extend _ _ HDyn) with
    | inl Hvalue =>
      generalize HEqe : open₀ Γ.length e = e𝕠
      rw [HEqe] at Hvalue H₁
      cases Hvalue with
      | code e Hlc =>
        exists st₀, .code (.lets b (close₀ Γ.length e))
        apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
        constructor
        apply typing_regular; apply H₀
        apply close_closedb; omega
        apply closedb_inc; apply Hlc; omega
        apply head𝕄.let𝕔
      | _ => contradiction
    | inr Hstep =>
      have ⟨st₁, _, Hstep⟩ := Hstep; exists st₁
      constructor
      apply stepℝ _ _ _ _ _ _ _ (ctxℝ.let𝕔 _ _); apply Hstep
      apply typing_regular; apply H₀
  case run =>
    intros _ _ _ _ _ _ Hclose IH HwellStore HDyn HEq𝕊
    right
    cases IH HwellStore HDyn with
    | inl Hvalue =>
      cases Hvalue with
      | code e Hlc =>
        exists st₀, e
        apply step_lvl.step𝕄 _ _ _ _ ctx𝕄.hole
        apply Hlc
        apply head𝕄.run
      | _ => contradiction
    | inr Hstep =>
      have ⟨st₁, _, Hstep⟩ := Hstep; exists st₁
      constructor
      apply stepℝ _ _ _ _ _ _ _ ctxℝ.run; apply Hstep
  case loc => intros; left; constructor
  case load₁ =>
    intros _ σ  _ _ _ H IH HwellStore HDyn HEq𝕊
    right
    cases IH HwellStore HDyn HEq𝕊 with
    | inl Hvalue =>
      cases Hvalue with
      | loc l =>
        cases H
        case loc HbindsLoc =>
          have HLt : l < σ.length :=
            by
            apply indexr_iff_lt.mpr
            constructor; apply HbindsLoc
          rw [HwellStore.left] at HLt
          have ⟨e, HbindsLoc⟩ := indexr_iff_lt.mp HLt
          exists st₀, e
          apply step_lvl.store𝕄 _ _ _ _ _ ctx𝕄.hole
          simp
          apply shead𝕄.load₁; apply HbindsLoc
      | _ => contradiction
    | inr Hstep =>
      have ⟨st₁, _, Hstep⟩ := Hstep; exists st₁
      apply step𝔹 _ _ _ _ _ _ ctx𝔹.load₁; apply Hstep
  case alloc₁ =>
    intros _ σ _ v _ H IH HwellStore HDyn HEq𝕊
    right
    cases IH HwellStore HDyn HEq𝕊 with
    | inl Hvalue =>
      exists v :: st₀, .loc st₀.length
      apply step_lvl.store𝕄 _ _ _ _ _ ctx𝕄.hole
      simp; apply typing_regular; apply H
      apply shead𝕄.alloc₁; apply Hvalue
    | inr Hstep =>
      have ⟨st₁, _, Hstep⟩ := Hstep; exists st₁
      apply step𝔹 _ _ _ _ _ _ ctx𝔹.alloc₁; apply Hstep
  case pure =>
    intros _ _ _ _ _ IH HwellStore HDyn
    apply IH; apply HwellStore; apply HDyn; rfl
  case reify =>
    intros _ _ _ _ _ _ IH HwellStore HDyn
    apply IH; apply HwellStore; apply HDyn; rfl
  apply Hτ

theorem progress :
  ∀ σ st₀ e₀ τ φ,
    well_store σ st₀ →
    typing_reification [] σ e₀ τ φ →
    value e₀ ∨ ∃ st₁ e₁, step (st₀, e₀) (st₁, e₁) :=
  by
  intros _ _ _ _ _ HwellStore Hτ
  rw [step, ← List.length_nil]
  apply progress_strengthened
  apply HwellStore; apply Hτ; simp
