#lang racket
(require redex)

(define-language
  vm
  (e x
     number
     (lam x e)
     (app₁ e e)
     (app₂ e e)
     (plus₁ e e)
     (plus₂ e e)
     (lift e)
     (code e)
     (reflect e)
     (lamc x e)
     (ifz₁ e e e)
     (fix₁ e)
     (fix₂ e)
     ;;; reify bound
     (lets x e e)
     (letc x e e)
     (run e)
     (ifz₂ e e e)
     )
  (E hole
     (app₁ E e) (app₁ v E)
     (app₂ E e) (app₂ v E)
     (plus₁ E e) (plus₁ v E)
     (plus₂ E e) (plus₂ v E)
     (lift E)
     (lets x E e)
     (ifz₁ E e e) (ifz₂ E e e)
     (fix₁ E) (fix₂ E))
  ;;; extended context, E without hole
  (E+
    (app₁ E e) (app₁ v E)
    (app₂ E e) (app₂ v E)
    (plus₁ E e) (plus₁ v E)
    (plus₂ E e) (plus₂ v E)
    (lift E)
    (lets x E e)
    (ifz₁ E e e) (ifz₂ E e e)
    (fix₁ E) (fix₂ E))
  (M hole
     (app₁ M e) (app₁ v M)
     (app₂ M e) (app₂ v M)
     (plus₁ M e) (plus₁ v M)
     (plus₂ M e) (plus₂ v M)
     (lift M)
     (lets x M e)
     (ifz₁ M e e) (ifz₂ M e e)
     (fix₁ M) (fix₂ M)
     ;;; reify context bound
     (lamc x M) (letc x e M) (run M)
     (ifz₂ v M e) (ifz₂ v v M))
  (R
    (app₁ R e) (app₁ v R)
    (app₂ R e) (app₂ v R)
    (plus₁ R e) (plus₁ v R)
    (plus₂ R e) (plus₂ v R)
    (lift R)
    (lets x R e)
    (ifz₁ R e e) (ifz₂ R e e)
    (fix₁ R) (fix₂ R)
    ;;; reify context bound
    (lamc x P) (letc x e P) (run P)
    (ifz₂ v P e) (ifz₂ v v P))
  (P hole
     (app₁ R e) (app₁ v R)
     (app₂ R e) (app₂ v R)
     (plus₁ R e) (plus₁ v R)
     (plus₂ R e) (plus₂ v R)
     (lift R)
     (lets x R e)
     (ifz₁ R e e) (ifz₂ R e e)
     (fix₁ R) (fix₂ R)
     ;;; reify context bound
     (lamc x P) (letc x e P) (run P)
     (ifz₂ v P e) (ifz₂ v v P))
  (v number (lam x e) (code e))
  (x variable-not-otherwise-mentioned))

(define not-code? (lambda (x) (not ((redex-match vm (code e)) x))))

(define red
  (reduction-relation
    vm
    (--> (in-hole M (lets x v e)) (in-hole M (subst x v e)) "lets")
    (--> (in-hole M (app₁ (lam x e) v)) (in-hole M (subst x v e)) "app₁")
    (--> (in-hole M (app₂ (code e_1) (code e_2))) (in-hole M (reflect (app₁ e_1 e_2))) "app₂")
    (--> (in-hole M (plus₁ number_1 number_2)) (in-hole M ,(+ (term number_1) (term number_2))) "plus₁")
    (--> (in-hole M (plus₂ (code e_1) (code e_2))) (in-hole M (reflect (plus₁ e_1 e_2))) "plus₂")
    (--> (in-hole M (lift number_1)) (in-hole M (code number_1)) "lift_lit")
    (--> (in-hole M (lift (lam x e))) (in-hole M (lamc x (subst x (code x) e))) "lift_lam")
    (--> (in-hole M (lamc x (code e))) (in-hole M (reflect (lam x e))) "lamc")
    (--> (in-hole M (letc x e_1 (code e_2))) (in-hole M (code (lets x e_1 e_2))) "letc_code")
    ;;; extended letc rules
    ;;; letc_value equivalent to:
    ;;; P⟦E⟦let𝕔 x e v⟧⟧ --> P⟦let𝕔 x e E⟦v⟧⟧
    ;;; where v != code _
    ;;;       E != hole
    (--> (in-hole P (in-hole E+ (letc x e v))) (in-hole P (letc x e (in-hole E+ v))) "letc_value"
         (side-condition (not-code? (term v))))
    (--> (in-hole M (run (code e))) (in-hole M e) "run")
    (--> (in-hole M (ifz₁ 0 e_1 e_2)) (in-hole M e_1) "ifz₁_0")
    (--> (in-hole M (ifz₁ number_0 e_1 e_2)) (in-hole M e_2) "ifz₁_n"
         (side-condition (not (= 0 (term number_0)))))
    (--> (in-hole M (ifz₂ (code e_1) (code e_2) (code e_3))) (in-hole M (reflect (ifz₁ e_1 e_2 e_3))) "ifz₂")
    (--> (in-hole M (fix₁ (lam x e))) (in-hole M (subst x (fix₁ (lam x e)) e)) "fix₁")
    (--> (in-hole M (fix₂ (code e))) (in-hole M (reflect (fix₁ e))) "fix₂")
    (--> (in-hole P (in-hole E (reflect e))) (in-hole P (letc x_new e (in-hole E (code x_new)))) "reflect"
         (where x_new ,(variable-not-in (term (P E e)) (term x))))
    ))

(define-metafunction
  vm
  subst : x any any -> any
  [(subst x_1 any_1 (lam x_1 any_2)) (lam x_1 any_2)]
  [(subst x_1 any_1 (lam x_2 any_2))
   (lam x_new (subst x_1 any_1 (subst-var x_2 x_new any_2)))
   (where x_new ,(variable-not-in (term (x_1 any_1 any_2)) (term x_2)))
   ]
  [(subst x_1 any_1 (lets x_1 any_x any_2)) (lets x_1 (subst x_1 any_1 any_x) any_2)]
  [(subst x_1 any_1 (lets x_2 any_x any_2))
   (lets x_new (subst x_1 any_1 any_x) (subst x_1 any_1 (subst-var x_2 x_new any_2)))
   (where x_new ,(variable-not-in (term (x_1 any_1 any_2)) (term x_2)))]
  [(subst x_1 any_1 (letc x_1 any_x any_2)) (letc x_1 (subst x_1 any_1 any_x) any_2)]
  [(subst x_1 any_1 (letc x_2 any_x any_2))
   (letc x_new (subst x_1 any_1 any_x) (subst x_1 any_1 (subst-var x_2 x_new any_2)))
   (where x_new ,(variable-not-in (term (x_1 any_1 any_2)) (term x_2)))]
  [(subst x_1 any_1 x_1) any_1]
  [(subst x_1 any_1 x_2) x_2]
  [(subst x_1 any_1 (any_2 ...))
   ((subst x_1 any_1 any_2) ...)]
  [(subst x_1 any_1 any_2) any_2])

(define-metafunction
  vm
  subst-var : x any any -> any
  [(subst-var x_1 any_1 x_1) any_1]
  [(subst-var x_1 any_1 (any_2 ...))
   ((subst-var x_1 any_1 any_2) ...)]
  [(subst-var x_1 any_1 any_2) any_2])

;;; ifz₂ example
(stepper
  red
  (term
    (lets x 0
          (lets y (ifz₂ (plus₂ (lift 1) (lift 1))
                        (plus₂ (lift 2) (lift 2))
                        (plus₂ (lift 3) (lift 3)))
                x)
          )))

;;; reflect example
(traces
  red
  (term
    (plus₁
      1
      (lets x (reflect (plus₁ 1 1)) 2)))
  )

;;; reflect stuck example
(stepper
  red
  (term
    (plus₁
      1
      (letc x1 (plus₁ 1 1) 2)))
  )

;;; sum (-10) + (-9)... + 0
(stepper
  red
  (term
    (app₁
      (fix₁
        (lam sum
             (lam x
                  (ifz₁ x
                        0
                        (plus₁
                          x
                          (app₁ sum (plus₁ x 1)))))
             )
        )
      -10)
    )
  )

;;; staged sum
(stepper
  red
  (term
    (app₁
      (fix₁
        (lam sum
             (lam x
                  (ifz₁ x
                        (lift 0)
                        (plus₂
                          (lift x)
                          (app₁ sum (plus₁ x 1)))))
             )
        )
      -10)
    )
  )

;;; staged sum₂
(stepper
  red
  (term
    (app₂
      (fix₂
        (lift
          (lam sum
               (lift
                 (lam x
                      (ifz₂ x
                            (lift 0)
                            (plus₂
                              x
                              (app₂ sum (plus₂ x (lift 1)))))))
               )
          )
        )
      (lift -10)))
  )

;;; avoid side effects duplication
(stepper
  red
  (term
    (lets f
          (letc x eff
                (lam y (code 1)))
          (plus₂ (app₁ f 0) (app₁ f 0))))
  )

;;; side effects discard
(stepper
  red
  (term
    (lets y
          (letc x eff
                (code 1))
          1))
  )

(stepper
  red
  (term (lets y (code eff) 1)))

;;; reify

(stepper
  red
  (term
    (run
      ;;; reify here!
      (letc x (plus₁ 0 1)
            (letc x1 (plus₁ x 2)
                  (code x1)))
      ))
  )

(stepper
  red
  (term
    (ifz₂
      (code 0)
      (code 0)
      ;;; reify here!
      (letc x (plus₁ 0 1)
            (letc x1 (plus₁ x 2)
                  (code x1)))
      ))
  )

