#lang racket
(require redex)

(define-language
  vm
  (e x
     (lam x e)
     (app₁ e e)
     (app₂ e e)
     (lit number)
     (plus₁ e e)
     (plus₂ e e)
     (lift e)
     (code e)
     (reflect e)
     (lamc x e)
     ;;; reify bound
     (lets x e e)
     (letc x e e)
     (run e)
     )
  (E hole
     (app₁ E e) (app₁ v E)
     (app₂ E e) (app₂ v E)
     (plus₁ E e) (plus₁ v E)
     (plus₂ E e) (plus₂ v E)
     (lift E) (lets x E e))
  (M hole
     (app₁ M e) (app₁ v M)
     (app₂ M e) (app₂ v M)
     (plus₁ M e) (plus₁ v M)
     (plus₂ M e) (plus₂ v M)
     (lift M) (lets x M e)
     (lamc x M) (letc x e M) (run M))
  (R
    (app₁ R e) (app₁ v R)
    (app₂ R e) (app₂ v R)
    (plus₁ R e) (plus₁ v R)
    (plus₂ R e) (plus₂ v R)
    (lift R) (lets x R e)
    ;;; reify context bound
    (lamc x P) (letc x e P) (run P))
  (P hole
     (app₁ R e) (app₁ v R)
     (app₂ R e) (app₂ v R)
     (plus₁ R e) (plus₁ v R)
     (plus₂ R e) (plus₂ v R)
     (lift R) (lets x R e)
     ;;; reify context bound
     (lamc x P) (letc x e P) (run P))
  (v (lit number) (lam x e) (code e))
  (x variable-not-otherwise-mentioned))

(define red
  (reduction-relation
    vm
    (--> (in-hole M (lets x v e)) (in-hole M (subst x v e)) "lets")
    (--> (in-hole M (app₁ (lam x e) v)) (in-hole M (subst x v e)) "app₁")
    (--> (in-hole M (app₂ (code e_1) (code e_2))) (in-hole M (reflect (app₁ e_1 e_2))) "app₂")
    (--> (in-hole M (plus₁ (lit number_1) (lit number_2))) (in-hole M (lit ,(+ (term number_1) (term number_2)))) "plus₁")
    (--> (in-hole M (plus₂ (code e_1) (code e_2))) (in-hole M (reflect (plus₁ e_1 e_2))) "plus₂")
    (--> (in-hole M (lift (lit number_1))) (in-hole M (code (lit number_1))) "lift_lit")
    (--> (in-hole M (lift (lam x e))) (in-hole M (lamc x (subst x (code x) e))) "lift_lam")
    (--> (in-hole M (lamc x (code e))) (in-hole M (reflect (lam x e))) "lamc")
    (--> (in-hole M (letc x e_1 (code e_2))) (in-hole M (code (lets x e_1 e_2))) "letc")
    (--> (in-hole P (in-hole E (reflect e))) (in-hole P (letc x_new e (in-hole E (code x_new)))) "reflect"
         (where x_new ,(variable-not-in (term (P E e)) (term x))))
    (--> (in-hole M (run (code e))) (in-hole M e) "run")
    ))

(define-metafunction
  vm
  subst : x v any -> any
  [(subst x_1 v (lam x_1 any_2)) (lam x_1 any_2)]
  [(subst x_1 v (lam x_2 any_2))
   (lam x_new (subst x_1 v (subst-var x_2 x_new any_2)))
   (where x_new ,(variable-not-in (term (x_1 v any_2)) (term x_2)))
   ]
  [(subst x_1 v (let x_1 any_x any_2)) (let x_1 (subst x_1 v any_x) any_2)]
  [(subst x_1 v (let x_2 any_x any_2))
   (let x_new (subst x_1 v any_x) (subst x_1 v (subst-var x_2 x_new any_2)))
   (where x_new ,(variable-not-in (term (x_1 v any_2)) (term x_2)))]
  [(subst x_1 v (letc x_1 any_x any_2)) (letc x_1 (subst x_1 v any_x) any_2)]
  [(subst x_1 v (letc x_2 any_x any_2))
   (letc x_new (subst x_1 v any_x) (subst x_1 v (subst-var x_2 x_new any_2)))
   (where x_new ,(variable-not-in (term (x_1 v any_2)) (term x_2)))]
  [(subst x_1 v x_1) v]
  [(subst x_1 v x_2) x_2]
  [(subst x_1 v (any_2 ...))
   ((subst x_1 v any_2) ...)]
  [(subst x_1 v any_2) any_2])

(define-metafunction
  vm
  subst-var : x any any -> any
  [(subst-var x_1 any_1 x_1) any_1]
  [(subst-var x_1 any_1 (any_2 ...))
   ((subst-var x_1 any_1 any_2) ...)]
  [(subst-var x_1 any_1 any_2) any_2])

(traces red (term (run (lets x (plus₂ (lift (lit 1)) (lift (lit 2))) x))))

