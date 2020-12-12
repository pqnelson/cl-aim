(defpackage #:cl-aim.fol.lcf-tests
  (:import-from #:cl-aim.fol.formula prop implies iff contradiction
                lor land l-neg verum
                predicate equals
                exists forall)
  (:import-from #:cl-aim.fol.term fn var)
  (:import-from #:cl-aim.fol.thm thm make-thm thm-statement)
  (:local-nicknames (#:axiom #:cl-aim.fol.axiom))
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
    (ok (equal? (implies-insert q (make-thm (implies p r)))
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
    (let ((p (prop 'p))
          (q (prop 'q)))
      (ok (equal? (ex-falso p)
                  (make-thm (implies contradiction p))))
      (ok (equal? (ex-falso (implies p q))
                  (make-thm (implies contradiction (implies p q)))))))

(deftest test-implies-transitivity-2
  (let ((p (prop 'p))
        (q (prop 'q))
        (r (prop 'r))
        (s (prop 's)))
    (ok (equal? (implies-transitivity-2
                 (make-thm (implies p (implies q r)))
                 (make-thm (implies r s)))
                (make-thm (implies p (implies q s)))))))

(deftest test-implies-transitivity-chain
  (let ((p (prop 'p))
        (q1 (prop 'q1))
        (q2 (prop 'q2))
        (q3 (prop 'q3))
        (r (prop 'r)))
    (ok (equal?
         (implies-transitivity-chain
          (list (make-thm (implies p q1))
                (make-thm (implies p q2))
                (make-thm (implies p q3)))
          (make-thm (implies q1 (implies q2 (implies q3 r)))))
         (make-thm (implies p r))))))

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
(deftest test-truth
  (ok (equal? (truth)
              (make-thm verum))))

(deftest test-contrapositive
  (let ((p (prop 'p))
        (q (prop 'q)))
    (ok (equal? (contrapositive (make-thm (implies p q)))
                (make-thm (implies (l-neg q) (l-neg p)))))))

(deftest test-and-left
  (ok (equal? (and-left (prop 'p) (prop 'q))
              (make-thm (implies (land (prop 'p) (prop 'q))
                                 (prop 'p))))))

(deftest test-and-right
  (ok (equal? (and-right (prop 'p) (prop 'q))
              (make-thm (implies (land (prop 'p) (prop 'q))
                                 (prop 'q))))))

(deftest test-conj-thms
  (let* ((p (prop 'p))
         (q (prop 'q))
         (r (prop 'r))
         (s (prop 's))
         (pqrs (land p q r s)))
    (ok (equal? (conj-thms (land p q r s))
                (mapcar #'(lambda (fm)
                            (make-thm (implies pqrs fm)))
                        (list p q r s))))))

(deftest test-expand-hypothesis
  (let ((p (prop 'p))
        (q (prop 'q))
        (r (prop 'r)))
    (ok (equal? (expand-hypothesis (make-thm (implies (land p q) r)))
                (make-thm (implies p (implies q r)))))))

(deftest test-contract-hypothesis
  (let ((p (prop 'p))
        (q (prop 'q))
        (r (prop 'r)))
    (ok (equal? (contract-hypothesis (make-thm (implies p (implies q r))))
                (make-thm (implies (land p q) r))))))

(deftest test-implies-false-consequents
  (let ((p (prop 'p))
        (q (prop 'q)))
    (ok (equal?
         (implies-false-consequents p q)
         (list
          (make-thm
           (implies (implies (implies p q) contradiction) p))
          (make-thm
           (implies (implies (implies p q) contradiction)
                    (implies q contradiction))))))))

(deftest test-implies-false-rule
  (let ((p (prop 'p))
        (q (prop 'q))
        (r (prop 'r)))
    (ok (equal?
         (implies-false-rule
          (make-thm (implies p (implies (implies q contradiction) r))))
         (make-thm
          (implies (implies (implies p q) contradiction) r))))))

(deftest test-implies-true-rule
  (let ((p (prop 'p))
        (q (prop 'q))
        (r (prop 'r)))
    (ok (equal?
         (implies-true-rule
          (make-thm (implies (implies p contradiction) r))
          (make-thm (implies q r)))
         (make-thm (implies (implies p q) r)))))
  )

(deftest test-implies-contradiction
  (let ((p (prop 'p))
        (q (prop 'q))
        (r (prop 'r)))
    (ok (equal?
         (implies-contradiction p q)
         (make-thm (implies p (implies (implies p contradiction)
                                       q)))))
    (ok (equal?
         (implies-contradiction (negate-formula p) q)
         (make-thm (implies (implies p contradiction)
                            (implies p q)))))))

;; TODO: finish this...
(deftest test-implies-front-th
  (labels ((range (n)
             (loop for k from 0 to n by 1
                   collect k))
           (int-to-prop (n)
             (prop (intern (concatenate 'string "p" (write-to-string n)))))
           (generate-props (n)
             (append (mapcar #'(lambda (x) (int-to-prop x)) (range n))
                     (prop 'q))))
    ;; (implies-front-th 3 (reduce #'implies (generate-props 10) :from-end t))
    )
  )

;; TODO test implies-front

(deftest test-iff-def
  (let ((p (prop 'p))
        (q (prop 'q)))
    (ok (equal? (thm-statement (iff-def p q))
                (iff (iff p q)
                     (land (implies p q)
                           (implies q p)))))))

(deftest test-expand-connective
  (ok (equal? (thm-statement (expand-connective verum))
              (iff verum
                   (implies contradiction contradiction))))
  (let ((p (prop 'p))
        (q (prop 'q)))
    (ok (equal? (thm-statement (expand-connective (l-neg p)))
                (iff (l-neg p)
                     (implies p contradiction))))
    (ok (equal? (thm-statement (expand-connective (land p q)))
                (iff (land p q)
                     (implies (implies p
                                       (implies q contradiction))
                              contradiction))))
    (ok (equal? (thm-statement (expand-connective (lor p q)))
                (iff (lor p q)
                     (l-neg (land (l-neg p) (l-neg q))))))
    (ok (equal? (expand-connective (iff p q))
                (iff-def p q))))
  ;; Buggy?
  (let ((x (var 'x))
        (p (lambda (v) (predicate 'p (list v)))))
    (ok (equal? (thm-statement (expand-connective
                                (exists x (funcall p x))))
                (iff (exists x (funcall p x))
                     (l-neg (forall x (l-neg (funcall p x)))))))
    ))

;; eliminate-connective
;; implies-false-consequents
;; implies-false-rule

(deftest test-tableau
  (let ((p (prop 'p))
        (q (prop 'q)))
    (ok (equal?
         (thm-statement
          (tableaux (list (negate-formula (iff (land p q)
                                               (iff (iff p q)
                                                    (lor p q)))))
                    nil))
         (implies (implies (iff (land p q)
                                (iff (iff p q)
                                     (lor p q)))
                           contradiction)
                  contradiction)))))

(deftest test-tautology
  (let ((p (prop 'p))
        (q (prop 'q)))
    (ok (equal? (thm-statement (tautology (lor (implies p q) (implies q p))))
                (lor (implies p q) (implies q p))))
    (ok (equal? (thm-statement (tautology (iff (land p q)
                                               (iff (iff p q)
                                                    (lor p q)))))
                (iff (land p q)
                     (iff (iff p q)
                          (lor p q)))))))

;;; First-order logic
(deftest test-equals-symmetry
  (let ((r (fn 'r nil))
        (s (fn 's nil)))
    (ok (equal? (equals-symmetry r s)
                (make-thm (implies (equals r s)
                                   (equals s r)))))))

(deftest test-equals-transitivity
  (let ((q (fn 'q nil))
        (r (fn 'r nil))
        (s (fn 's nil)))
    (equal? (equals-transitivity q r s)
            (make-thm (implies (equals q r)
                               (implies (equals r s)
                                        (equals q s)))))))

(deftest test-term-congruence
  (let* ((x (var 'x))
         (y (var 'y))
         (z (var 'z))
         (lhs (fn 'f (list x (fn 'g (list x y x)) z (fn 'h (list x)))))
         (rhs (fn 'f (list x (fn 'g (list y y x)) z (fn 'h (list y))))))
    (testing "The terms are the variables themselves"
      (ok (term-congruence x y x y)))
    (testing "Terms are equal"
      (ok (typep (term-congruence x y x x) 'thm))
      (ok (term-congruence x y lhs lhs))
      (ok (term-congruence x y rhs rhs)))
    (testing "Expressions are functions"
      (ok (typep (term-congruence x y lhs rhs) 'thm)))))

(deftest test-axiom-generalize-right
  (let ((x (var 'x))
        (p (prop 'p))
        (q (predicate 'q (list (var 'x)))))
    (ok (equal? (thm-statement (axiom-generalize-right x p q))
                (implies (forall x (implies p q))
                         (implies p (forall x q))))))
  (testing "When x is a bound-variable in P"
    (let ((x (var 'x))
          (p (exists (var 'x)
                     (predicate 'p (list (var 'x)))))
          (q (predicate 'q (list (var 'x)))))
      (ok (equal? (thm-statement (axiom-generalize-right x p q))
                  (implies (forall x (implies p q))
                           (implies p (forall x q)))))))
  (testing "Gen-right when bound-variable is not x"
    (let ((x (var 'x))
          (p (exists (var 'x)
                     (predicate 'p (list (var 'x)))))
          (q (predicate 'q (list (var 'y)))))
      (ok (equal? (thm-statement (axiom-generalize-right x p q))
                  (implies (forall x (implies p q))
                           (implies p (forall x q))))))))

(deftest test-generalize-implies
  (let* ((x (var 'x))
         (p (predicate 'p (list (var 'x))))
         (q (predicate 'q (list (var 'x))))
         (th ))
    (ok (typep (generalize-implies x (make-thm (implies p q))) 'thm))
    (ok (equal? (thm-statement
                 (generalize-implies x (make-thm (implies p q))))
                (implies (forall x p)
                         (forall x q))))))

(deftest test-generalize-right
  (let ((x (var 'x))
        (p (prop 'p))
        (q (predicate 'q (list (var 'x)))))
    (ok (equal? (thm-statement (generalize-right x (make-thm (implies p q))))
                (implies p (forall x q))))))
        
(deftest test-axiom-exists-left
  (let ((x (var 'x))
        (p (predicate 'p (list (var 'x))))
        (q (prop 'q)))
    (ok (equal? (thm-statement (axiom-exists-left x p q))
                (implies (forall x (implies p q))
                         (implies (exists x p)
                                  q))))))

(deftest test-exists-left
  (let ((x (var 'x))
        (p (predicate 'p (list (var 'x))))
        (q (prop 'q)))
    (ok (equal? (thm-statement (exists-left x (make-thm (implies p q))))
                (implies (exists x p) q)))))
