(defpackage #:cl-aim.fol.lcf-tests
  (:import-from #:cl-aim.fol.formula prop implies iff contradiction)
  (:import-from #:cl-aim.fol.thm make-thm)
  (:use #:cl #:cl-aim.utils #:rove #:cl-aim.fol.lcf))
(in-package #:cl-aim.fol.lcf-tests)

(deftest test-implies-reflexivity
  (ok (equal? (implies-reflexivity (prop 'p))
              (make-thm (implies (prop 'p) (prop 'p))))))

(deftest test-implies-unduplicate
  (let ((pq (implies (prop 'p) (prop 'q)))
        (ppq (implies (prop 'p) (implies (prop 'p) (prop 'q)))))
    (ok (equal? (implies-unduplicate (make-thm ppq))
                (make-thm pq)))))

(deftest test-add-assume
  (let ((p (prop 'p))
        (th (make-thm (prop 'q))))
    (ok (equal? (add-assume p th)
                (make-thm (implies p (prop 'q)))))))

(deftest test-implies-add-assume
  (let ((p (prop 'p))
        (q (prop 'q))
        (r (prop 'r)))
    (ok (equal? (implies-add-assume p (make-thm (implies q r)))
                (make-thm (implies (implies p q)
                                   (implies p r)))))))

(deftest test-implies-transitivity
  (let ((p (prop 'p))
        (q (prop 'q))
        (r (prop 'r)))
    (ok (equal? (implies-transitivity (make-thm (implies p q))
                                      (make-thm (implies q r)))
                (make-thm (implies p r))))))

(deftest test-implies-insert
  (let ((p (prop 'p))
        (q (prop 'q))
        (r (prop 'r)))
    (ok (equal? (implies-insert (make-thm q) (make-thm (implies p r)))
                (make-thm (implies p (implies q r)))))))

(deftest test-implies-swap
  (let ((p (prop 'p))
        (q (prop 'q))
        (r (prop 'r)))
    (ok (equal? (implies-swap (make-thm (implies p (implies q r))))
                (make-thm (implies q (implies p r)))))))

(deftest test-axiom-implies-transitivity
  (let ((p (prop 'p))
        (q (prop 'q))
        (r (prop 'r)))
    (ok (equal? (axiom-implies-transitivity p q r)
                (make-thm (implies (implies q r)
                                   (implies (implies p q)
                                            (implies p r)))))))
  )

(deftest test-implies-add-conclusion
  (let ((p (prop 'p))
        (q (prop 'q))
        (r (prop 'r)))
    (ok (equal? (implies-add-conclusion r (make-thm (implies p q)))
                (make-thm (implies (implies q r)
                                   (implies p r))))))
  )


(deftest test-axiom-implies-swap
  (let ((p (prop 'p))
        (q (prop 'q))
        (r (prop 'r)))
    (ok (equal? (axiom-implies-swap p q r)
                (make-thm (implies (implies p (implies q r))
                                   (implies q (implies p r)))))))
  )

(deftest test-implies-double-swap
  (let* ((p (prop 'p))
         (q (prop 'q))
         (r (prop 'r))
         (s (prop 's))
         (tt (prop 't))
         (u (prop 'u))
         (pqr (implies p (implies q r)))
         (stu (implies s (implies tt u)))
         (qpr (implies q (implies p r)))
         (tsu (implies tt (implies s u))))
    (ok (equal? (implies-double-swap (make-thm (implies pqr stu)))
                (make-thm (implies qpr tsu))))
    ))

(deftest test-right-modus-ponens
  (let* ((p (prop 'p))
         (q (prop 'q))
         (r (prop 'r))
         (th (make-thm (implies p q)))
         (th-implies-r (make-thm (implies p (implies q r)))))
    (ok (equal? (right-modus-ponens th-implies-r th)
                (make-thm (implies p r))))))

(deftest test-iff->left-implies
  (let ((p (prop 'p))
        (q (prop 'q)))
    (ok (equal? (iff->left-implies (make-thm (iff p q)))
                (make-thm (implies p q))))))

(deftest test-iff->right-implies
  (let ((p (prop 'p))
        (q (prop 'q)))
    (ok (equal? (iff->right-implies (make-thm (iff p q)))
                (make-thm (implies q p))))))

(deftest test-implies-antisymmetric
  (let ((p (prop 'p))
        (q (prop 'q)))
    (ok (equal? (implies-antisymmetric (make-thm (implies p q))
                                       (make-thm (implies q p)))
                (make-thm (iff p q))))))

(deftest test-double-negation
  (let ((p (prop 'p))
        (q (prop 'q)))
    (ok (equal? (double-negation
                 (make-thm (implies p
                                    (implies (implies q contradiction)
                                             contradiction))))
                (make-thm (implies p q))))))

(deftest test-ex-falso
  (let ((p (prop 'p)))
    (ok (equal? (ex-falso p)
                (make-thm (implies contradiction p))))))

(deftest test-implies-transitivity-2
  (let ((p (prop 'p))
        (q (prop 'q))
        (r (prop 'r))
        (s (prop 's)))
    (ok (equal? (implies-transitivity-2
                 (make-thm (implies p (implies q r)))
                 (make-thm (implies r s)))
                (make-thm (implies p (implies q s)))))))

(deftest test-not-q-and-p-and-p-implies-q-derives-contradiction
  (let ((p (prop 'p))
        (q (prop 'q)))
    (ok (equal? (not-q-and-p-and-p-implies-q-derives-contradiction p q)
                (make-thm
                 (implies (implies q contradiction)
                          (implies p
                                   (implies (implies p q)
                                            contradiction))))))))

;; (deftest test-axiom-implies-monotonic
;;   (let ((p (prop 'p))
;;         (p% (prop 'p%))
;;         (q (prop 'q))
;;         (q% (prop 'q%)))
;;     (ok (equal?
;;          (axiom-implies-monotonic p p% q q%)
;;          (make-thm (implies
;;                     (implies #pred(P%) #pred(P))
;;                     (implies (implies #pred(Q) #pred(Q%))
;;                              (implies (implies #pred(P) #pred(Q))
;;                                       (implies #pred(P%) #pred(Q%))))))))))
  
