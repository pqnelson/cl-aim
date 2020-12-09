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
           expand-hypothesis contract-hypothesis
           iff-def expand-connective
           implies-true-rule
           implies-false-consequents implies-false-rule implies-contradiction
           tableaux tautology
           equals-symmetry equals-transitivity)
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
  (declare (type thm p-implies-r)
           (type formula q))
  (let ((p (implies-premise (thm-statement p-implies-r)))
        (r (implies-conclusion (thm-statement p-implies-r))))
    (implies-transitivity p-implies-r (axiom:add-implies r q))))

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
  
;;;; Tableau prover.
;;;;
;;;; We need some small engine to prove theorems, and tableau are
;;;; simple enough for us to get cooking.

(defun iff-def (p q)
  "Establishes `|- (p iff q) iff (and (p => q) (q => p))'."
  (declare (type formula p q))
  (implies-antisymmetric
   (implies-transitivity-chain
    (list (axiom:iff->left-implies p q) (axiom:iff->right-implies p q))
    (and-pair (implies p q) (implies q p)))
   (contract-hypothesis (axiom:implies->iff p q))))

;; CRITICAL: this is necessary for propositional tableau method
(defun expand-connective (fm)
  (declare (type formula fm))
  (typecase fm
    (verum-type (axiom:true))
    (negation (axiom:negate (negation-argument fm)))
    (l-and (apply #'axiom:expand-and* (l-and-conjuncts fm)))
    (l-or (apply #'axiom:expand-or* (l-or-disjuncts fm)))
    (iff (iff-def (iff-premise fm) (iff-conclusion fm)))
    (exists (axiom:exists-iff-not-forall-not (exists-var fm) (exists-body fm)))
    (t (error "Expand connective failed with ~A" fm))))

(defun eliminate-connective (fm)
  (declare (type formula fm))
  (if (negative? fm)
      (implies-add-conclusion contradiction
                              (iff->right-implies
                               (expand-connective (negate-formula fm))))
      (iff->left-implies (expand-connective fm))))

(defun implies-false-consequents (p q)
  (declare (type formula p q))
  (list
   (double-negation (implies-add-conclusion
                     contradiction
                     (implies-add-assume p (ex-falso q))))
   (implies-add-conclusion contradiction
                           (implies-insert p (implies-reflexivity q)))
   ))

(defun implies-false-rule (th)
  "From `|- p => (q => false) => r' infer `|- ((p => q) => false) => r'."
  (declare (type thm-implies th))
  (let* ((p (implies-premise (thm-statement th)))
         (r (implies-conclusion (thm-statement th)))
         (q (implies-premise (implies-premise r))))
    (implies-transitivity-chain
     (implies-false-consequents p q)
     th)))

(defun implies-true-rule (th1 th2)
  "From `|- (p => false) => r' and `|- q => r' infer `|- (p => q) => r'."
  (declare (type thm-implies th1 th2))
  (let* ((p (implies-premise (implies-premise (thm-statement th1))))
         (q (implies-premise (thm-statement th2)))
         (nr->p (double-negation (implies-add-conclusion contradiction th1)))
         (nr->nq (implies-add-conclusion contradiction th2))
         (p->nq->not-pq (implies-swap (not-q-and-p-and-p-implies-q-derives-contradiction p q)))
         )
    (double-negation
     (implies-transitivity
      (implies-swap (implies-reflexivity (implies (implies p q) contradiction)))
      (implies-add-conclusion contradiction
                              (implies-transitivity-chain (list nr->p nr->nq)
                                                          p->nq->not-pq))))
    ))

(defun implies-contradiction (p q)
  (declare (type formula p q))
  (if (negative? p)
      (implies-add-assume (negate-formula p) (ex-falso q))
      (implies-swap (implies-add-assume p (ex-falso q)))))

(defun implies-front-th (n fm)
  (declare (type implies fm)
           (type integer n))
  (if (not (plusp n))
      (implies-reflexivity fm)
      (let* ((p (implies-premise fm))
             (qr (implies-conclusion fm))
             (th1 (implies-add-assume p (implies-front-th (1- n) qr)))
             (q% (implies-premise
                  (implies-conclusion (implies-conclusion (thm-statement th1)))))
             (r% (implies-conclusion
                  (implies-conclusion (implies-conclusion (thm-statement th1)))))
             )
        (implies-transitivity th1 (axiom-implies-swap p q% r%))
        ))
    )

(defun implies-front (n th)
  (modus-ponens (implies-front-th n (thm-statement th)) th))

(defun atom-tableau (p fl ls)
  (declare (type formula p)
           (type (or null (cons formula)) fl ls))
  (if (member (negate-formula p) ls :test #'equal?)
      (let* ((neg-p (negate-formula p))
             (parted-lits (partition-by
                           #'(lambda (x)
                               (equal? neg-p x))
                           ls))
             (l1 (car parted-lits))
             (l2 (cadr parted-lits))
             (th (implies-contradiction
                  p
                  (reduce #'implies (cdr l2)
                                    :initial-value contradiction
                                    :from-end t))))
        (reduce #'implies-insert (append fl l1)
                :initial-value th
                :from-end t))
      (implies-front (length fl) (tableaux fl (cons p ls)))))

(defun atom-t-ex1 ()
  (let ((p (prop 'p))
        (q (prop 'q)))
    (atom-tableau p
                  (list (implies p contradiction))
                  (list q p (implies q contradiction)))))

(defun atom-tabl-ex0 ()
  (let ((p (prop 'p))
        (q (prop 'q)))
    (atom-tableau p (list (implies q contradiction)) (list q))))



;; seems good?
(defun default-tableau (fm fl ls)
  (declare (type formula p)
           (type (or null (cons formula)) fl ls))
  (let ((th (eliminate-connective fm)))
    (implies-transitivity th (tableaux
                              (cons (implies-conclusion
                                     (thm-statement th))
                                    fl)
                              ls))))
(defun default-tab-ex1 ()
  (let ((p (prop 'p))
        (q (prop 'q)))
    (default-tableau
     (lor p q)
     (list (implies p contradiction))
     (list p p (implies p contradiction) p))))

;; Given a list of formulas FMS and literals LITS
;; we have an inferential form of tableaux.
;; Should produce a thm object.
(defun tableaux (fms lits)
  (declare (type (or null (cons formula)) fms lits))
  (typecase (car fms)
    (contradiction-type (ex-falso (reduce #'implies
                                          (append (cdr fms) lits)
                                          :initial-value contradiction
                                          :from-end t)))
    (implies (let ((p (implies-premise (car fms)))
                   (q (implies-conclusion (car fms))))
               (cond
                 ;; fm = (implies p p)
                 ((equal? p q)
                  ;; seems good
                  (add-assume (car fms) (tableaux (cdr fms) lits)))
                 ;; fm = (implies (implies p0 q0) contradiction)
                 ((and (implies? p) (contradiction? q))
                  ;; seems good
                  (let ((p0 (implies-premise p))
                        (q0 (implies-conclusion p)))
                    (implies-false-rule
                     (tableaux
                      (cons p0 (cons (implies q0 contradiction) (cdr fms)))
                      lits))))
                 ;; (implies p q) but (not= p q) and (not= q contradiction)
                 ((not (contradiction? q))
                  ;; seems good
                  (implies-true-rule (tableaux (cons (implies p contradiction)
                                                     (cdr fms))
                                               lits)
                                     (tableaux (cons q (cdr fms)) lits)))
                 ((and (contradiction? q)
                       (forall? p))
                  (atom-tableau (car fms) (cdr fms) lits))
                 ((and (contradiction? q)
                       (predicate? p))
                  (atom-tableau (car fms) (cdr fms) lits))
                 (t (default-tableau (car fms) (cdr fms) lits)))))
    (predicate (atom-tableau (car fms) (cdr fms) lits))
    (forall    (atom-tableau (car fms) (cdr fms) lits))
    ;; (prop-literal (atom-tableau (car fms) (cdr fms) lits))
    (formula   (default-tableau (car fms) (cdr fms) lits))
    (t         (error "LCF Tableaux: no contradiction for ~A" (car fms)))))

(defun tableaux-ex0 ()
  (let ((p (prop 'p))
        (q (prop 'q)))
    (tableaux (list p (implies q contradiction)) nil)))

(defun tautology (p)
  "Infer if P is a tautology or not. If not, raises an error. Warning: slow."
  (declare (type formula p))
  (modus-ponens (axiom:double-negation p)
                (tableaux (list (negate-formula p)) nil)))

;;;; First-order derived rules.

;; tested
(defun equals-symmetry (r s)
  "For any terms R and S, infer `|- (s = t) => (t = s)'."
  (declare (type term r s))
  (let ((rth (axiom:equals-reflexive r))
        (p-cong (axiom:predicate-congruence (lambda (xs)
                                              (apply #'cl-aim.fol.formula:equals xs))
                                            (list r r)
                                            (list s r))))
    (modus-ponens (implies-swap (modus-ponens (implies-swap p-cong) rth))
                  rth)
    ))

(defun equals-transitivity (q r s)
  "Infer `|- (Q = R) => (R = S) => (Q = S)'."
  (declare (type term q r s))
  (let* ((th1 (axiom:predicate-congruence
               (lambda (xs)
                 (apply #'equals xs))
               (list r s)
               (list q s)))
         (th2 (modus-ponens (implies-swap th1)
                            (axiom:equals-reflexive s))))
    (implies-transitivity (equals-symmetry q r) th2)))



