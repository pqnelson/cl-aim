(defpackage #:cl-aim.fol.hilbert
  (:use #:cl #:cl-aim.utils #:cl-aim.fol.formula #:cl-aim.fol.term)
;;  (:shadow-import-from )
  (:import-from #:cl-aim.fol.thm thm thm? thm-statement make-thm thm-implies)
  (:import-from #:cl-aim.fol.axiom defaxiom modus-ponens generalize)
  (:local-nicknames (#:axiom #:cl-aim.fol.axiom))
  (:documentation "A Hilbert calculus based LCF prover.

Good references for LCF provers in general include
- John Harrison's slides `The LCF Approach to Theorem Proving' and
  his book on Automated Reasoning;
- Jon Sterling's example using sequent calculus;"))
(in-package #:cl-aim.fol.hilbert)

;;;; Hilbert system axioms.
;;;;
;;;; We begin by listing out the axioms for the Hilbert calculus. These
;;;; are schemas, i.e., they take non-theorems and will produce a theorem.
;;;; They are our only way to generate theorems. We use inference rules to
;;;; map theorems to theorems, axioms to map non-theorems to theorems.
(defaxiom add-implies (p q)
  "Axiom `|- p => (q => p)'."
  (declare (type formula p q))
  (make-thm (implies p (implies q p))))

(defaxiom distribute-implies (p q r)
  (declare (type formula p q r))
  (make-thm (implies (implies p (implies q r))
                     (implies (implies p q) (implies p r)))))

(defaxiom double-negation (p)
  (declare (type formula p))
  (make-thm (implies (implies (implies p contradiction)
                              contradiction)
                     p)))

(defaxiom forall-implies (x p q)
  (declare (type (or symbol var) x)
           (type formula p q))
  (make-thm (implies (forall (var x) (implies p q))
                     (implies (forall (var x) p)
                              (forall (var x) q)))))

(defaxiom implies-forall (x p)
  (declare (type (or symbol var) x)
           (type formula p))
  (if (free-in? x p)
      (error "Variable free in formula")
      (make-thm (implies p (forall (var x) p)))))

(defaxiom exists-equals (x tm)
  "If X is a fresh variable, asserts there is an X equal to TM."
  (declare (type (or var symbol) x)
           (type term tm))
  (if (occurs-in? (var x) tm)
      (error "Variable")
      (make-thm (exists (var x) (equals (var x) tm)))))

(defaxiom equals-reflexive (tm)
  (declare (type term tm))
  (make-thm (equals tm tm)))

(defun zip-terms (lefts rights end-hook last-connective)
  (labels ((pop-term (ls rs)
             (assert (eq (endp (cdr ls)) (endp (cdr rs))))
             (assert (eq (null (car ls)) (null (car rs))))
             (when (null (car ls))
               (assert (eq (endp (car ls)) (endp (car rs)))))
             (when (car ls)
               (if (endp (cdr ls))
                   (implies (equals (car ls) (car rs))
                            (funcall last-connective
                                     (funcall end-hook lefts)
                                     (funcall end-hook rights)))
                   (implies (equals (car ls) (car rs))
                            (pop-term (cdr ls) (cdr rs)))))))
    (pop-term lefts rights)))

(defaxiom fun-congruence (f lefts rights)
  (declare (type symbol f)
           (type (or null (cons term)) lefts rights))
  ;; |- l1 = r1 => l2 = r2 => ... => l-last = r-last => (f lefts) = (f rights)
  (if (null lefts)
      (progn (assert (null rights))
             (make-thm (equals (fn f nil) (fn f nil))))
      (make-thm (zip-terms lefts
                           rights
                           (lambda (args)
                             (fn f args))
                           #'equals)))
  )

(defaxiom predicate-congruence (p lefts rights)
  ;; |- l1 = r1 => l2 = r2 => ... => l-last = r-last => (P lefts) = (P rights)
  (declare (type symbol p)
           (type (or null (cons term)) lefts rights))
  (if (null lefts)
      (progn (assert (null rights))
             (make-thm (implies (predicate p nil) (predicate p nil))))
      (make-thm (zip-terms lefts
                           rights
                           (lambda (args)
                             (predicate p args))
                           #'implies)))
  )

(defaxiom iff->left-implies (p q)
  (declare (type formula p q))
  (make-thm (implies (iff p q)
                     (implies p q))))

(defaxiom iff->right-implies (p q)
  (declare (type formula p q))
  (make-thm (implies (iff p q)
                     (implies q p))))

(defaxiom implies->iff (p q)
  (declare (type formula p q))
  (make-thm (implies (implies p q)
                     (implies (implies q p)
                              (iff p q)))))

(defaxiom true ()
  (make-thm (iff verum (implies contradiction contradiction))))

(defaxiom negate (p)
  (declare (type formula p))
  (make-thm (iff (l-neg p)
                 (implies p contradiction))))

(defaxiom expand-and (p q)
  (declare (type formula p q))
  (make-thm (iff (land p q)
                 (implies (implies p (implies q contradiction))
                          contradiction))))

(defaxiom expand-or (p q)
  (declare (type formula p q))
  (format t "~% package: ~A" (package-name *package*))
  (make-thm (iff (lor p q)
                 (l-neg (land (l-neg p) (l-neg q))))))

(defaxiom exists-iff-not-forall-not (x p)
  (declare (type (or var symbol) x)
           (type formula p))
  (make-thm (iff (exists (var x) p)
                 (l-neg (forall (var x) (l-neg p))))))

