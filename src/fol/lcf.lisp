(defpackage #:cl-aim.fol.lcf
  (:use #:cl #:cl-aim.utils #:cl-aim.fol.formula #:cl-aim.fol.term)
  (:import-from #:cl-aim.fol.thm thm thm? thm-statement make-thm thm-implies)
  (:import-from #:cl-aim.fol.axiom modus-ponens generalize)
  (:local-nicknames (#:axiom #:cl-aim.fol.axiom))
  (:export implies-reflexivity implies-unduplicate negative? negate-formula
           add-assume implies-add-assume implies-transitivity implies-insert
           implies-swap axiom-implies-transitivity implies-add-conclusion
           axiom-implies-swap implies-double-swap right-modus-ponens
           iff->left-implies iff->right-implies implies-antisymmetric
           double-negation ex-falso implies-transitivity-2
           implies-transitivity-chain
           not-q-and-p-and-p-implies-q-derives-contradiction
           axiom-implies-monotonic
           truth contrapositive and-left and-right conj-thms
           expand-hypothesis contract-hypothesis)
  )
(in-package #:cl-aim.fol.lcf)

;;; We have just defined the axioms for the Hilbert system, and we assume
;;; modus ponens and generalization are the only inference rules permitted.
;;; 
;;; Now we introduce an axiom schema, `implies-reflexivity', which takes a
;;; formula and produces a theorem; and then we start working through the
;;; derived inference rules.

(defun implies-reflexivity (p)
  "For any formula P, we always have (implies P P)."
  (declare (type formula p))
  (modus-ponens (modus-ponens (axiom:distribute-implies p (implies p p) p)
                              (axiom:add-implies p (implies p p)))
                (axiom:add-implies p p)))

(defun implies-unduplicate (th)
  "From `|- p => (p => q)' infer `|- (p => q)'."
  (declare (type thm-implies th))
  (assert (implies? (implies-conclusion (thm-statement th))))
  (let* ((p-implies-p-implies-q (thm-statement th))
         (p (implies-premise p-implies-p-implies-q))
         (p-implies-q (implies-conclusion p-implies-p-implies-q))
         (q (implies-conclusion p-implies-q)))
    (modus-ponens (modus-ponens (axiom:distribute-implies p p q)
                                th)
                  (implies-reflexivity p))))

;;;; Elementary derived rules.
;;;;
;;;; We already have introduced a couple derived rules, like
;;;; `implies-reflexivity' and `implies-unduplicate'. 

(defun negative? (fm)
  "Negated formulas in the Hilbert calculus look like `P => contradiction'."
  (declare (type formula fm))
  (and (implies? fm)
       (eq contradiction (implies-conclusion fm))))

(defun negate-formula (fm)
  "From `fm' produce `not fm'.

Handles double negation as: from `not fm' infer `fm'."
  (declare (type formula fm))
  (if (negative? fm)
      (implies-premise fm) ;; double-negation 
      (implies fm contradiction)))

(defun add-assume (p th)
  "From `|- q' we can infer `|- p => q'."
  (declare (type formula p)
           (type thm th))
  (modus-ponens (axiom:add-implies (thm-statement th) p)
                th))

(defun implies-add-assume (p q-implies-r)
  "From any formula `p' and thm `|- q => r' infer `|- (p => q) => (p => r)'."
  (declare (type formula p)
           (type thm q-implies-r))
  (assert (implies? (thm-statement q-implies-r)))
  (let ((q (implies-premise (thm-statement q-implies-r)))
        (r (implies-conclusion (thm-statement q-implies-r))))
    (modus-ponens (axiom:distribute-implies p q r)
                  (add-assume p q-implies-r))))

(defun implies-transitivity (p-implies-q q-implies-r)
  "From `|- p => q' and `|- q => r' infer `|- p => r'."
  (declare (type thm-implies p-implies-q q-implies-r))
  (let ((p (implies-premise (thm-statement p-implies-q))))
    (modus-ponens (implies-add-assume p q-implies-r)
                  p-implies-q)))

(defun implies-insert (q p-implies-r)
  "From `|- q' and `|- p => r' infer `|- p => (q => r)'."
  (declare (type thm q p-implies-r))
  (let ((p (implies-premise (thm-statement p-implies-r)))
        (r (implies-conclusion (thm-statement p-implies-r))))
    (implies-transitivity p-implies-r (axiom:add-implies r (thm-statement q)))))

(defun implies-swap (p-implies-q-implies-r)
  "From `|- p => (q => r)' infer `|- q => (p => r)'.

This is because the formula is equivalent to `|- (and p q) => r'."
  (declare (type thm-implies p-implies-q-implies-r))
  (let* ((p (implies-premise (thm-statement p-implies-q-implies-r)))
         (q-implies-r (implies-conclusion
                       (thm-statement p-implies-q-implies-r)))
         (q (implies-premise q-implies-r))
         (r (implies-conclusion q-implies-r)))
    (implies-transitivity (axiom:add-implies q p)
                          (modus-ponens (axiom:distribute-implies p q r)
                                        p-implies-q-implies-r))))

(defun axiom-implies-transitivity (p q r)
  "For any formula P, Q, R, we have `|- (q => r) => (p => q) => (p => r)."
  (declare (type formula p q r))
  (implies-transitivity (axiom:add-implies (implies q r) p)
                        (axiom:distribute-implies p q r)))

(defun implies-add-conclusion (r th)
  "If `|- p => q' then `|- (q => r) => (p => r)'."
  (declare (type formula r)
           (type thm-implies th))
  (let ((p (implies-premise (thm-statement th)))
        (q (implies-conclusion (thm-statement th))))
    (modus-ponens (implies-swap (axiom-implies-transitivity p q r))
                  th)
    )
  )

(defun axiom-implies-swap (p q r)
  "Derived axiom `|- (p => q => r) => (q => p => r)'."
  (declare (type formula p q r))
  (implies-transitivity
   (axiom:distribute-implies p q r)
   (implies-add-conclusion (implies p r)
                           (axiom:add-implies q p))))

(defun implies-double-swap (th)
  "Given `|- (p => q => r) => (s => t => u)' infer 
`|- (q => p => r) => (t => s => u)'."
  (declare (type thm-implies th))
  (let* ((pqr (implies-premise (thm-statement th)))
         (p (implies-premise pqr))
         (q (implies-premise (implies-conclusion pqr)))
         (r (implies-conclusion (implies-conclusion pqr)))
         (stu (implies-conclusion (thm-statement th)))
         (s (implies-premise stu))
         (tt (implies-premise (implies-conclusion stu)))
         (u (implies-conclusion (implies-conclusion stu))))
    (implies-transitivity (axiom-implies-swap q p r)
                          (implies-transitivity
                           th
                           (axiom-implies-swap s tt u)))))

(defun right-modus-ponens (th-implies-r th)
  "From `|- p => q => r' and `|- p => q' infer `|- p => r'."
  (declare (type thm-implies th-implies-r th))
  (implies-unduplicate (implies-transitivity th
                                             (implies-swap th-implies-r))))

(defun iff->left-implies (th)
  "From `|- p iff q' infer `|- p => q'."
  (declare (type thm th))
  (let ((p (iff-premise (thm-statement th)))
        (q (iff-conclusion (thm-statement th))))
    (modus-ponens (axiom:iff->left-implies p q) th)))

(defun iff->right-implies (th)
  "From `|- p iff q' infer `|- q => p'."
  (declare (type thm th))
  (let ((p (iff-premise (thm-statement th)))
        (q (iff-conclusion (thm-statement th))))
    (modus-ponens (axiom:iff->right-implies p q) th)))

(defun implies-antisymmetric (th-pq th-qp)
  "From `|- p => q' and `|- q => p' infer `| p iff q'."
  (declare (type thm-implies th-pq th-qp))
  (let ((p (implies-premise (thm-statement th-pq)))
        (q (implies-conclusion (thm-statement th-pq))))
    (modus-ponens (modus-ponens (axiom:implies->iff p q)
                                th-pq)
                  th-qp)))

(defun double-negation (th)
  "Infer from `|- p => (q => FALSE) => FALSE' that `|- p => q'."
  (declare (type thm-implies th))
  (let ((q (implies-premise
            (implies-premise (implies-conclusion (thm-statement th))))))
    (implies-transitivity th (axiom:double-negation q))))

(defun ex-falso (p)
  "For any formula P, we have `|- FALSE => p'."
  (declare (type formula p))
  (double-negation (axiom:add-implies contradiction
                                      (implies p contradiction))))

(defun implies-transitivity-2 (th-pqr th-rs)
  "Given `|- p => q => r' and `|- r => s', infer `|- p => q => s'."
  (let ((p (implies-premise (thm-statement th-pqr)))
        (q (implies-premise (implies-conclusion (thm-statement th-pqr))))
        (r (implies-premise (thm-statement th-rs)))
        (s (implies-conclusion (thm-statement th-rs))))
    (modus-ponens (implies-add-assume p
                                      (modus-ponens
                                       (axiom-implies-transitivity q r s)
                                       th-rs))
                  th-pqr)))

;; Needed for `contract-hypothesis'.
(defun implies-transitivity-chain (ths th)
  "From thms `|- p => q_i' for i=1..N, and `|- q_1 => ... => q_N => r',
 infer `|- p => r'."
  (declare (type (cons thm-implies) ths)
           (type thm-implies th))
  (reduce #'(lambda (current-thm a)
              (implies-unduplicate
               (implies-transitivity a (implies-swap current-thm))))
          (cdr ths)
          :initial-value (implies-transitivity (car ths) th)))


(defun not-q-and-p-and-p-implies-q-derives-contradiction (p q)
  "For any formulas P and Q, infers `|- (q => F) => p => (p => q) => F'."
  (declare (type formula p q))
  (implies-transitivity
   (axiom-implies-transitivity p q contradiction)
   (axiom-implies-swap (implies p q) p contradiction)))

(defun axiom-implies-monotonic (p p% q q%)
  "Establishes `|- (p% => p) => (q => q%) => (p => q) => (p% => q%)'."
  (declare (type formula p p% q q%))
  (let ((th1 (axiom-implies-transitivity (implies p q)
                                         (implies p% q)
                                         (implies p% q%)))
        (th2 (axiom-implies-transitivity p% q q%))
        (th3 (implies-swap (axiom-implies-transitivity p% p q)))
        )
    (implies-transitivity th3
                          (implies-swap
                           (implies-transitivity th2 th1)))))

(defun truth ()
  "Establishes `|- verum.'"
  (modus-ponens (iff->right-implies (axiom:true))
                (implies-reflexivity contradiction)))

(defun contrapositive (th)
  "From `|- p => q' infer `|- (not q) => (not p)'."
  (declare (type thm-implies th))
  (let ((p (implies-premise (thm-statement th)))
        (q (implies-conclusion (thm-statement th))))
    (implies-transitivity
     (implies-transitivity (iff->left-implies (axiom:negate q))
                           (implies-add-conclusion contradiction th))
     (iff->right-implies (axiom:negate p)))))

(defun and-left (p q)
  "For any P, Q we have `|- (and P Q) => P'."
  (declare (type formula p q))
  (let ((np-p-q-contradiction (implies-add-assume
                               p
                               (axiom:add-implies contradiction q))))
    (implies-transitivity (iff->left-implies
                           (axiom:expand-and p q))
                          (double-negation
                           (implies-add-conclusion
                            contradiction
                            np-p-q-contradiction)))))

(defun and-right (p q)
  "For any P, Q we have `|- (and P Q) => Q'."
  (declare (type formula p q))
  (let ((nq-p-nq (axiom:add-implies (implies q contradiction)
                                    p)))
    (implies-transitivity
     (iff->left-implies (axiom:expand-and p q))
     (double-negation (implies-add-conclusion contradiction nq-p-nq)
                      ))))

(defun conj-thms (fm)
  "For any conjunction `(land p_1 ... p_N)', we have a list of N thm
`|- (land p_1 .. p_n) => p_j' for j=1, ..., N."
  (declare (type formula fm))
  (if (land? fm)
      (let ((p (car (l-and-conjuncts fm)))
            (qs (apply #'land (remove-if #'null (cdr (l-and-conjuncts fm))))))
        (cons (and-left p qs)
              (if (not (land? qs))
                  (list (implies-transitivity
                         (and-right p qs)
                         (implies-reflexivity qs)))
                  (mapcar #'(lambda (th)
                              ;; th = |- (and q_i .. q_n) => q_j
                              (implies-transitivity
                               (and-right p qs)
                               th))
                          (conj-thms qs)))))
      (list (implies-reflexivity fm))))

(defun and-pair (p q)
  "For any formulas P and Q, we have `|- p => q => (p and q)'."
  (declare (type formula p q))
  (let* ((th1 (iff->right-implies (axiom:expand-and p q)))
         (th2 (axiom-implies-swap (implies p (implies q contradiction))
                                  q
                                  contradiction))
         (th3 (implies-add-assume p (implies-transitivity-2 th2 th1))))
    (modus-ponens th3
                  (implies-swap
                   (implies-reflexivity
                    (implies p (implies q contradiction)))))))

(defun expand-hypothesis (th)
  "Transform `|- (and p q) => r' into `|- p => (q => r)'."
  (declare (type thm-implies th))
  (let* ((p-and-q (implies-premise (thm-statement th)))
         (p (car (l-and-conjuncts p-and-q)))
         (q (cadr (l-and-conjuncts p-and-q))))
    (assert (endp (cddr (l-and-conjuncts p-and-q))))
    (modus-ponens (reduce #'implies-add-assume
                          (l-and-conjuncts p-and-q)
                          :initial-value th
                          :from-end t)
                  (and-pair p q))))

(defun contract-hypothesis (th)
  "Transform `|- p => (q => r)' into `|- (and p q) => r'."
  (declare (type thm-implies th))
  (let ((p (implies-premise (thm-statement th)))
        (q (implies-premise (implies-conclusion (thm-statement th))))
        (r (implies-conclusion (implies-conclusion (thm-statement th)))))
    (implies-transitivity-chain (list (and-left p q)
                                      (and-right p q))
                                th)))
  
