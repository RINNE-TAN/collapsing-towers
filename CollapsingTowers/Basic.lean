
inductive UnaryOp : Type where
  | IsNum

inductive BinaryOp : Type where
  | Plus
  | Times

inductive Expr : Type where
  | Var (x : String)
  | Lit (i : Int)
  | Lam (f : String) (x : String) (e : Expr)
  | App (f : Expr) (arg : Expr)
  | Cons (head : Expr) (tails : Expr)
  | Let (x : String) (binds : Expr) (e : Expr)
  | If (condition : Expr) (branch₀ : Expr) (branch₁ : Expr)
  | Unary (op : UnaryOp) (e : Expr)
  | Binary (op : BinaryOp) (e₀ : Expr) (e₁ : Expr)
  | Lift (e : Expr)
  | Run (ctrl : Expr) (code : Expr)
  | Code (e : Expr)
  | Reflect (e : Expr)
  | Lam𝕔 (f : String) (x : String) (e : Expr)
  | Let𝕔 (x : String) (binds : Expr) (e : Expr)

inductive value : Expr -> Prop where
  | value_lit : value (.Lit i)
  | value_lam : value (.Lam f x e)
  | value_cons : value head -> value tails -> value (.Cons head tails)
  | value_code : value (.Code e)

inductive free : String -> Expr -> Prop where
  | free_var : x = y -> free x (.Var y)
  | free_lam : x != f -> x != y -> free x e -> free x (.Lam f y e)
  | free_appL : free x f -> free x (.App f arg)
  | free_appR : free x arg -> free x (.App f arg)
  | free_consL : free x head -> free x (.Cons head tails)
  | free_consR : free x tails -> free x (.Cons head tails)
  | free_letL : free x binds -> free x (.Let y binds e)
  | free_letR : x != y -> free x e -> free x (.Let y binds e)
  | free_ifC : free x condition -> free x (.If condition branch₀ branch₁)
  | free_ifL : free x branch₀ -> free x (.If condition branch₀ branch₁)
  | free_ifR : free x branch₁ -> free x (.If condition branch₀ branch₁)
  | free_unary : free x e -> free x (.Unary op e)
  | free_binaryL : free x e₀ -> free x (.Binary op e₀ e₁)
  | free_binaryR : free x e₁ -> free x (.Binary op e₀ e₁)
  | free_lift : free x e -> free x (.Lift e)
  | free_runL : free x ctrl -> free x (.Run ctrl code)
  | free_runR : free x code -> free x (.Run ctrl code)
  | free_code : free x e -> free x (.Code e)
  | free_reflect : free x e -> free x (.Reflect e)
  | free_Lam𝕔 : x != f -> x != y -> free x e -> free x (.Lam𝕔 f y e)
  | free_Let𝕔L : free x binds -> free x (.Let𝕔 y binds e)
  | free_Let𝕔R : x != y -> free x e -> free x (.Let𝕔 y binds e)

abbrev Ctx :=
  Expr -> Expr

notation:max a "⟦" b "⟧" => a b

inductive freeCtx : String -> Ctx -> Prop where
  | freeCtx : ¬free x e -> free x Γ⟦e⟧ -> freeCtx x Γ

inductive ctx𝔹 : Ctx -> Prop where
  | ctx𝔹_consL : ctx𝔹 (fun X => .Cons X tails)
  | ctx𝔹_consR : value v -> ctx𝔹 (fun X => .Cons v X)
  | ctx𝔹_let : ctx𝔹 (fun X => .Let x X e)
  | ctx𝔹_appL : ctx𝔹 (fun X => .App X arg)
  | ctx𝔹_appR : value v -> ctx𝔹 (fun X => .App v X)
  | ctx𝔹_if : ctx𝔹 (fun X => .If X branch₀ branch₁)
  | ctx𝔹_unary : ctx𝔹 (fun X => .Unary op X)
  | ctx𝔹_binaryL : ctx𝔹 (fun X => .Binary op X e₁)
  | ctx𝔹_binaryR : value v -> ctx𝔹 (fun X => .Binary op v X)
  | ctx𝔹_lift : ctx𝔹 (fun X => .Lift X)
  | ctx𝔹_run : ctx𝔹 (fun X => .Run X code)
  | ctx𝔹_reflect : ctx𝔹 (fun X => .Reflect X)

inductive ctxℝ : Ctx -> Prop where
  | ctxℝ_liftLam𝕔 : ctxℝ (fun X => .Lift (.Lam𝕔 f x X))
  | ctxℝ_ifL : ctxℝ (fun X => .If (.Code condition) X branch₁)
  | ctxℝ_ifR : value v -> ctxℝ (fun X => .If (.Code condition) v X)
  | ctxℝ_run : value v -> ctxℝ (fun X => .Run v X)
  | ctxℝ_Let𝕔 : ctxℝ (fun X => .Let𝕔 x e X)

inductive ctx𝕄 : Ctx -> Prop where
  | ctx𝕄_hole : ctx𝕄 (fun X => X)
  | ctx𝕄_𝔹 : ctx𝔹 B -> ctx𝕄 M -> ctx𝕄 (B ∘ M)
  | ctx𝕄_ℝ : ctxℝ R -> ctx𝕄 M -> ctx𝕄 (R ∘ M)

inductive ctx𝔼 : Ctx -> Prop where
  | ctx𝔼_hole : ctx𝔼 (fun X => X)
  | ctx𝔼_𝔹 : ctx𝔹 B -> ctx𝔼 E -> ctx𝔼 (B ∘ E)

mutual
  inductive ctxℙ : Ctx -> Prop where
    | ctxℙ_hole : ctxℙ (fun X => X)
    | ctxℙ_𝔹 : ctx𝔹 B -> ctxℚ Q -> ctxℙ (B ∘ Q)
    | ctxℙ_ℝ : ctxℝ R -> ctxℙ P -> ctxℙ (R ∘ P)
  inductive ctxℚ : Ctx -> Prop where
    | ctxℚ_𝔹 : ctx𝔹 B -> ctxℚ Q -> ctxℚ (B ∘ Q)
    | ctxℚ_ℝ : ctxℝ R -> ctxℙ P -> ctxℚ (R ∘ P)
end

def subst (x : String) (v : Expr) (e : Expr) : Expr :=
  match e with
  | .Var y => if x == y then v else .Var y
  | .Lit i => .Lit i
  | .Lam f y e => if x == f || x == y then .Lam f y e else .Lam f y (subst x v e)
  | .App f arg => .App (subst x v f) (subst x v arg)
  | .Cons head tails => .Cons (subst x v head) (subst x v tails)
  | .Let y binds e => if x == y then .Let y binds e else .Let y binds (subst x v e)
  | .If condition branch₀ branch₁ => .If (subst x v condition) (subst x v branch₀) (subst x v branch₁)
  | .Unary op e => .Unary op (subst x v e)
  | .Binary op e₀ e₁ => .Binary op (subst x v e₀) (subst x v e₁)
  | .Lift e => .Lift (subst x v e)
  | .Run ctrl code => .Run (subst x v ctrl) (subst x v code)
  | .Code e => .Code (subst x v e)
  | .Reflect e => .Reflect (subst x v e)
  | .Lam𝕔 f y e => if x == f || x == y then .Lam𝕔 f y e else .Lam𝕔 f y (subst x v e)
  | .Let𝕔 y binds e => if x == y then .Let𝕔 y binds e else .Let𝕔 y binds (subst x v e)

inductive step : Expr -> Expr -> Prop where
  | step_letβ : ctx𝕄 M -> value v -> step M⟦.Let x v e⟧ M⟦subst x v e⟧
  | step_appβ : ctx𝕄 M -> value v -> step M⟦.Let x v e⟧ M⟦subst x v e⟧
  | step_app𝕔 : ctx𝕄 M -> step M⟦.App (.Code f) (.Code arg)⟧ M⟦.Reflect (.App f arg)⟧
  | step_ifnz : ctx𝕄 M -> n != 0 -> step M⟦.If (.Lit n) branch₀ branch₁⟧ M⟦branch₀⟧
  | step_ifz : ctx𝕄 M -> step M⟦.If (.Lit 0) branch₀ branch₁⟧ M⟦branch₁⟧
  |
  step_if𝕔 :
    ctx𝕄 M -> step M⟦.If (.Code condition) (.Code branch₀) (.Code branch₁)⟧ M⟦.Reflect (.If condiction branch₀ branch₁)⟧
  | step_isNum : ctx𝕄 M -> value v -> v = .Lit n -> step M⟦.Unary .IsNum v⟧ M⟦(.Lit 1)⟧
  | step_notNum₀ : ctx𝕄 M -> value v -> v = .Lam f arg e -> step M⟦.Unary .IsNum v⟧ M⟦(.Lit 0)⟧
  | step_notNum₁ : ctx𝕄 M -> value v -> v = .Cons head tails -> step M⟦.Unary .IsNum v⟧ M⟦(.Lit 0)⟧
  | step_isNum𝕔 : ctx𝕄 M -> step M⟦.Unary .IsNum (.Code e)⟧ M⟦(.Reflect (.Unary .IsNum e))⟧
  | step_plus : ctx𝕄 M -> step M⟦.Binary .Plus (.Lit n₀) (.Lit n₁)⟧ M⟦.Lit (n₀ + n₁)⟧
  | step_times : ctx𝕄 M -> step M⟦.Binary .Times (.Lit n₀) (.Lit n₁)⟧ M⟦.Lit (n₀ * n₁)⟧
  | step_binary𝕔 : ctx𝕄 M -> step M⟦.Binary op (.Code e₀) (.Code e₁)⟧ M⟦.Reflect (.Binary op e₀ e₁)⟧
  | step_lit : ctx𝕄 M -> step M⟦.Lift (.Lit n)⟧ M⟦.Code (.Lit n)⟧
  | step_cons : ctx𝕄 M -> step M⟦.Lift (.Cons (.Code head) (.Code tails))⟧ M⟦.Reflect (.Cons head tails)⟧
  |
  step_lam {M f arg e} :
    ctx𝕄 M ->
      step M⟦.Lift (.Lam f arg e)⟧ M⟦.Lift (.Lam𝕔 f arg (subst arg (.Code (.Var arg)) (subst f (.Code (.Var f)) e)))⟧
  | step_lam𝕔 : ctx𝕄 M -> step M⟦.Lift (.Lam𝕔 f arg (.Code e))⟧ M⟦.Reflect (.Lam f arg e)⟧
  | step_code : ctx𝕄 M -> step M⟦.Lift (.Code e)⟧ M⟦.Reflect (.Lift e)⟧
  | step_run₀ : ctx𝕄 M -> value v -> v = .Lit _ -> step M⟦.Run v (.Code code)⟧ M⟦code⟧
  | step_run₁ : ctx𝕄 M -> value v -> v = .Lam _ _ _ -> step M⟦.Run v (.Code code)⟧ M⟦code⟧
  | step_run₂ : ctx𝕄 M -> value v -> v = .Cons _ _ -> step M⟦.Run v (.Code code)⟧ M⟦code⟧
  | step_run𝕔 : ctx𝕄 M -> step M⟦.Run (.Code ctrl) (.Code code)⟧ M⟦.Reflect (.Run ctrl code)⟧
  | step_reflect : ctxℙ P -> ctx𝔼 E -> ¬freeCtx x E -> step P⟦E⟦.Reflect e⟧⟧ P⟦.Let𝕔 x e E⟦.Code (.Var x)⟧⟧
  | step_let𝕔 : ctx𝕄 M -> step M⟦.Let𝕔 x binds (.Code e)⟧ M⟦.Code (.Let x binds e)⟧

inductive mulit : Expr -> Expr -> Prop where
  | multi_stop : mulit e e
  | multi_step : step e₀ e₁ -> mulit e₁ e₂ -> mulit e₀ e₂

theorem mulit_trans : mulit e₀ e₁ -> mulit e₁ e₂ -> mulit e₀ e₂ :=
  by
  intro me₀e₁
  induction me₀e₁ with
  | multi_stop => simp
  | multi_step se₀e₃ _ ih =>
    intro me₁e₂
    constructor
    apply se₀e₃
    apply ih
    apply me₁e₂

def expr₀ : Expr :=
  .Lift (.Lam "f" "x" (.Binary .Plus (.Var "x") (.Binary .Times (.Var "x") (.Var "x"))))

def expr₁ : Expr :=
  .Lift (.Lam𝕔 "f" "x" (.Binary .Plus (.Code (.Var "x")) (.Binary .Times (.Code (.Var "x")) (.Code (.Var "x")))))

def step₀ : step expr₀ expr₁ := by
  rw [expr₀]
  rw [expr₁]
  apply (step.step_lam ctx𝕄.ctx𝕄_hole)

def expr₂ : Expr :=
  .Lift (.Lam𝕔 "f" "x" (.Binary .Plus (.Code (.Var "x")) (.Reflect (.Binary .Times (.Var "x") (.Var "x")))))

def step₁ : step expr₁ expr₂ := by
  rw [expr₁]
  rw [expr₂]
  apply
    (step.step_binary𝕔
      (ctx𝕄.ctx𝕄_ℝ ctxℝ.ctxℝ_liftLam𝕔 (ctx𝕄.ctx𝕄_𝔹 (ctx𝔹.ctx𝔹_binaryR value.value_code) (ctx𝕄.ctx𝕄_hole))))

def expr₃ : Expr :=
  .Lift
    (.Lam𝕔 "f" "x"
      (.Let𝕔 "x₁" (.Binary .Times (.Var "x") (.Var "x")) (.Binary .Plus (.Code (.Var "x")) (.Code (.Var "x₁")))))

def step₂ : step expr₂ expr₃ := by
  rw [expr₂]
  rw [expr₃]
  apply
    (step.step_reflect (ctxℙ.ctxℙ_ℝ ctxℝ.ctxℝ_liftLam𝕔 ctxℙ.ctxℙ_hole)
      (ctx𝔼.ctx𝔼_𝔹 (ctx𝔹.ctx𝔹_binaryR value.value_code) ctx𝔼.ctx𝔼_hole))
  intro hfreeCtx
  cases hfreeCtx with
  | freeCtx ihbind ihfree =>
    apply ihbind
    simp at ihfree
    cases ihfree with
    | free_binaryL ihfree =>
      cases ihfree with
      | free_code ihfree =>
        cases ihfree with
        | _ => contradiction
    | free_binaryR ihfree => apply ihfree

def expr₄ : Expr :=
  .Lift
    (.Lam𝕔 "f" "x"
      (.Let𝕔 "x₁" (.Binary .Times (.Var "x") (.Var "x")) (.Reflect (.Binary .Plus (.Var "x") (.Var "x₁")))))

def step₃ : step expr₃ expr₄ := by
  rw [expr₃]
  rw [expr₄]
  apply (step.step_binary𝕔 (ctx𝕄.ctx𝕄_ℝ ctxℝ.ctxℝ_liftLam𝕔 (ctx𝕄.ctx𝕄_ℝ (ctxℝ.ctxℝ_Let𝕔) (ctx𝕄.ctx𝕄_hole))))

def expr₅ : Expr :=
  .Lift
    (.Lam𝕔 "f" "x"
      (.Let𝕔 "x₁" (.Binary .Times (.Var "x") (.Var "x"))
        (.Let𝕔 "x₂" (.Binary .Plus (.Var "x") (.Var "x₁")) (.Code (.Var "x₂")))))

def step₄ : step expr₄ expr₅ := by
  rw [expr₄]
  rw [expr₅]
  apply
    (step.step_reflect (ctxℙ.ctxℙ_ℝ ctxℝ.ctxℝ_liftLam𝕔 (ctxℙ.ctxℙ_ℝ ctxℝ.ctxℝ_Let𝕔 ctxℙ.ctxℙ_hole)) (ctx𝔼.ctx𝔼_hole))
  intro hfreeCtx
  cases hfreeCtx with
  | freeCtx ihbind ihfree =>
    apply ihbind
    simp at ihfree
    apply ihfree

def expr₆ : Expr :=
  .Lift
    (.Lam𝕔 "f" "x"
      (.Let𝕔 "x₁" (.Binary .Times (.Var "x") (.Var "x"))
        (.Code (.Let "x₂" (.Binary .Plus (.Var "x") (.Var "x₁")) (.Var "x₂")))))

def step₅ : step expr₅ expr₆ := by
  rw [expr₅]
  rw [expr₆]
  apply (step.step_let𝕔 (ctx𝕄.ctx𝕄_ℝ ctxℝ.ctxℝ_liftLam𝕔 (ctx𝕄.ctx𝕄_ℝ (ctxℝ.ctxℝ_Let𝕔) (ctx𝕄.ctx𝕄_hole))))

def expr₇ : Expr :=
  .Lift
    (.Lam𝕔 "f" "x"
      (.Code
        (.Let "x₁" (.Binary .Times (.Var "x") (.Var "x"))
          (.Let "x₂" (.Binary .Plus (.Var "x") (.Var "x₁")) (.Var "x₂")))))

def step₆ : step expr₆ expr₇ := by
  rw [expr₆]
  rw [expr₇]
  apply (step.step_let𝕔 (ctx𝕄.ctx𝕄_ℝ ctxℝ.ctxℝ_liftLam𝕔 ctx𝕄.ctx𝕄_hole))

def expr₈ : Expr :=
  .Reflect
    (.Lam "f" "x"
      (.Let "x₁" (.Binary .Times (.Var "x") (.Var "x")) (.Let "x₂" (.Binary .Plus (.Var "x") (.Var "x₁")) (.Var "x₂"))))

def step₇ : step expr₇ expr₈ := by
  rw [expr₇]
  rw [expr₈]
  apply (step.step_lam𝕔 ctx𝕄.ctx𝕄_hole)

def expr₉ : Expr :=
  .Let𝕔 "x₃"
    (.Lam "f" "x"
      (.Let "x₁" (.Binary .Times (.Var "x") (.Var "x")) (.Let "x₂" (.Binary .Plus (.Var "x") (.Var "x₁")) (.Var "x₂"))))
    (.Code (.Var "x₃"))

def step₈ : step expr₈ expr₉ := by
  rw [expr₈]
  rw [expr₉]
  apply (step.step_reflect ctxℙ.ctxℙ_hole ctx𝔼.ctx𝔼_hole)
  intro hfreeCtx
  cases hfreeCtx with
  | freeCtx ihbind ihfree =>
    apply ihbind
    simp at ihfree
    apply ihfree

def exprₓ : Expr :=
  .Code
    (.Let "x₃"
      (.Lam "f" "x"
        (.Let "x₁" (.Binary .Times (.Var "x") (.Var "x"))
          (.Let "x₂" (.Binary .Plus (.Var "x") (.Var "x₁")) (.Var "x₂"))))
      (.Var "x₃"))

def step₉ : step expr₉ exprₓ := by
  rw [expr₉]
  rw [exprₓ]
  apply (step.step_let𝕔 ctx𝕄.ctx𝕄_hole)

theorem eval_expr₀ : mulit expr₀ exprₓ := by
  constructor
  apply step₀
  constructor
  apply step₁
  constructor
  apply step₂
  constructor
  apply step₃
  constructor
  apply step₄
  constructor
  apply step₅
  constructor
  apply step₆
  constructor
  apply step₇
  constructor
  apply step₈
  constructor
  apply step₉
  constructor
