import CollapsingTowers.TwoLevelMut.Syntax.Defs

inductive value : Expr → Prop where
  | lam : ∀ e, lc (.lam e) → value (.lam e)
  | lit : ∀ n, value (.lit n)
  | code : ∀ e, lc e → value (.code e)
  | unit : value .unit
  | loc : ∀ l, value (.loc l)

lemma lc.value : ∀ e, value e → lc e := by
  intro e Hvalue
  cases Hvalue with
  | lam _ Hclosed => apply Hclosed
  | lit => simp
  | code _ Hclosed => apply Hclosed
  | unit => simp
  | loc => simp

instance lc_at.decidable (e : Expr) (i : Nat) : Decidable (lc_at e i) :=
  match e with
  | .bvar j => if h : j < i then isTrue h else isFalse h
  | .fvar _ => isTrue (by simp)
  | .lam e => lc_at.decidable e (i + 1)
  | .lift e => lc_at.decidable e i
  | .app₁ f arg =>
    match lc_at.decidable f i, lc_at.decidable arg i with
    | isTrue Hf, isTrue Harg => isTrue ⟨Hf, Harg⟩
    | isFalse Hf, _ => isFalse (λ H => Hf H.left)
    | _, isFalse Harg => isFalse (λ H => Harg H.right)
  | .app₂ f arg =>
    match lc_at.decidable f i, lc_at.decidable arg i with
    | isTrue Hf, isTrue Harg => isTrue ⟨Hf, Harg⟩
    | isFalse Hf, _ => isFalse (λ H => Hf H.left)
    | _, isFalse Harg => isFalse (λ H => Harg H.right)
  | .lit _ => isTrue (by simp)
  | .run e => lc_at.decidable e i
  | .code e => lc_at.decidable e i
  | .reflect e => lc_at.decidable e i
  | .lam𝕔 e => lc_at.decidable e (i + 1)
  | .lets b e =>
    match lc_at.decidable b i, lc_at.decidable e (i + 1) with
    | isTrue Hb, isTrue He => isTrue ⟨Hb, He⟩
    | isFalse Hb, _ => isFalse (λ H => Hb H.left)
    | _, isFalse He => isFalse (λ H => He H.right)
  | .lets𝕔 b e =>
    match lc_at.decidable b i, lc_at.decidable e (i + 1) with
    | isTrue Hb, isTrue He => isTrue ⟨Hb, He⟩
    | isFalse Hb, _ => isFalse (λ H => Hb H.left)
    | _, isFalse He => isFalse (λ H => He H.right)
  | .unit => isTrue (by simp)
  | .loc _ => isTrue (by simp)
  | .alloc₁ e => lc_at.decidable e i
  | .alloc₂ e => lc_at.decidable e i
  | .load₁ e => lc_at.decidable e i
  | .load₂ e => lc_at.decidable e i
  | .store₁ l r =>
    match lc_at.decidable l i, lc_at.decidable r i with
    | isTrue Hl, isTrue Hr => isTrue ⟨Hl, Hr⟩
    | isFalse Hl, _ => isFalse (λ H => Hl H.left)
    | _, isFalse Hr => isFalse (λ H => Hr H.right)
  | .store₂ l r =>
    match lc_at.decidable l i, lc_at.decidable r i with
    | isTrue Hl, isTrue Hr => isTrue ⟨Hl, Hr⟩
    | isFalse Hl, _ => isFalse (λ H => Hl H.left)
    | _, isFalse r => isFalse (λ H => r H.right)

instance value.decidable (e : Expr) : Decidable (value e) :=
  match e with
  | .lam e =>
    match lc_at.decidable e 1 with
    | isTrue Hlc => isTrue (by apply value.lam; apply Hlc)
    | isFalse Hlc => isFalse (by intros Hvalue; apply Hlc; apply lc.value _ Hvalue)
  | .lit _ => isTrue (by apply value.lit)
  | .code e =>
    match lc_at.decidable e 0 with
    | isTrue Hlc => isTrue (by apply value.code; apply Hlc)
    | isFalse Hlc => isFalse (by intros Hvalue; apply Hlc; apply lc.value _ Hvalue)
  | .bvar _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .fvar _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .lift _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .app₁ _ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .app₂ _ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .run _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .reflect _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .lam𝕔 _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .lets _ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .lets𝕔 _ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .unit => isTrue (by apply value.unit)
  | .loc _ => isTrue (by apply value.loc)
  | .alloc₁ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .alloc₂ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .load₁ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .load₂ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .store₁ _ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .store₂ _ _ => isFalse (by intros Hvalue; nomatch Hvalue)
