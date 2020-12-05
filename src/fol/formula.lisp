(defpackage #:cl-aim.fol.formula
  (:use #:cl #:cl-aim.utils)
  (:import-from #:cl-aim.fol.term vars var term fn var-name term-subst)
  (:export iff implies land lor negate predicate forall exists
           verum contradiction vars free-vars
           equal? ->nnf term-subst
           pull-quantifiers))
(in-package #:cl-aim.fol.formula)

(defclass formula ()
  ())

(defclass implies (formula)
  ((premise :initarg :premise
            :initform (error "Implies must have a premise")
            :accessor implies-premise
            :type formula)
   (conclusion :initarg :conclusion
               :accessor implies-conclusion
               :initform (error "Implies must have a conclusion")
               :type formula)))

(defun implies (premise conclusion)
  (declare (type formula premise conclusion))
  (make-instance 'implies
                 :premise premise
                 :conclusion conclusion))

(defmethod print-object ((object implies) stream)
  (format stream "(#implies ~A ~A)" (implies-premise object)
          (implies-conclusion object)))

(defclass l-or (formula)
  ((disjuncts :initarg :disjuncts
              :accessor l-or-disjuncts
              :type (cons formula))))

(defmethod print-object ((object l-or) stream)
  (format stream "(#or ~A)" (l-or-disjuncts object)))

(defun lor (&rest disjuncts)
  (make-instance 'l-or :disjuncts disjuncts))

(defclass l-and (formula)
  ((conjuncts :initarg :conjuncts
              :accessor l-and-conjuncts
              :type (cons formula))))

(defmethod print-object ((object l-and) stream)
  (format stream "(#and ~A)" (l-and-conjuncts object)))

(defun land (&rest conjuncts)
  (make-instance 'l-and :conjuncts conjuncts))

(defclass negation (formula)
  ((argument :initarg :formula
             :accessor negation-argument
             :type formula)))

(defmethod print-object ((object negation) stream)
  (format stream "(#not ~A)" (negation-argument object)))

(defun negate (fm)
  (declare (type formula fm))
  (make-instance 'negation :formula fm))

(defclass iff (formula)
  ((premise :initarg :premise
            :accessor iff-premise
            :initform (error "Iff must have a premise")
            :type formula)
   (conclusion :initarg :conclusion
               :accessor iff-conclusion
               :initform (error "Iff must have a conclusion")
               :type formula)))

(defun iff (premise conclusion)
  (declare (type formula premise conclusion))
  (make-instance 'iff
                 :premise premise
                 :conclusion conclusion))

(defmethod print-object ((object iff) stream)
  (format stream "(#iff ~A ~A)" (iff-premise object)
          (iff-conclusion object)))

(defclass logical-constant (formula)
  ((name :type symbol
         :initarg :name
         :accessor logical-constant-name
         :reader constant-name)))

(defmethod print-object ((object logical-constant) stream)
  (format stream "#const(~A)" (logical-constant-name object)))

(unless (boundp 'verum)
  (defconstant verum (make-instance 'logical-constant :name 'verum)
    "Represents logical truth constant."))

(defun verum? (x)
  (eq x verum))

(unless (boundp 'contradiction)
  (defconstant contradiction (make-instance 'logical-constant :name 'contradiction)
    "The 'false' constant."))

(defun contradiction? (x)
  (eq contradiction x))

(defclass forall (formula)
  ((var :initarg :var
        :accessor forall-var
        :type cl-aim.fol.term:var)
   (body :initarg :body
         :accessor forall-body
         :type formula)))

(defmethod print-object ((object forall) stream)
  (format stream "(#forall ~A ~A)" (forall-var object)
          (forall-body object)))

(defun forall (x matrix)
  (declare (type formula matrix)
           (type (or symbol cl-aim.fol.term:var) x))
  (make-instance 'forall
                 :var (if (symbolp x)
                          (var x)
                          x)
                 :body matrix))

(defclass exists (formula)
  ((var :initarg :var
        :accessor exists-var
        :type cl-aim.fol.term:var)
   (body :initarg :body
         :accessor exists-body
         :type formula)))

(defmethod print-object ((object exists) stream)
  (format stream "(#exists ~A ~A)" (exists-var object)
          (exists-body object)))

(defun exists (x matrix)
  (declare (type formula matrix)
           (type (or symbol cl-aim.fol.term:var) x))
  (make-instance 'exists
                 :var (if (symbolp x)
                          (var x)
                          x)
                 :body matrix))

(defclass predicate (formula)
  ((name :initarg :name
         :accessor predicate-name)
   (args :initarg :args
         :accessor predicate-args
         :initform nil
         :type (or nil (cons cl-aim.fol.term:term)))))

(defmethod print-object ((object predicate) stream)
  (format stream "#pred(~A ~A)" (predicate-name object)
          (predicate-args object)))

;;; equal? tests if the formulas are equal or not, it's not deep.
(defmethod equal? ((lhs implies) (rhs implies))
  (and (equal? (implies-premise lhs) (implies-premise rhs))
       (equal? (implies-conclusion lhs) (implies-conclusion rhs))))

(defmethod equal? ((lhs iff) (rhs iff))
  (and (equal? (iff-premise lhs) (iff-premise rhs))
       (equal? (iff-conclusion lhs) (iff-conclusion rhs))))

(defmethod equal? ((lhs l-or) (rhs l-or))
  (list-equal? (l-or-disjuncts lhs)
               (l-or-disjuncts rhs)))

(defmethod equal? ((lhs l-and) (rhs l-and))
  (list-equal? (l-and-conjuncts lhs)
               (l-and-conjuncts rhs)))

(defmethod equal? ((lhs negation) (rhs negation))
  (equal? (negation-argument lhs) (negation-argument rhs)))

(defmethod equal? ((lhs forall) (rhs forall))
  (and (equal? (forall-var lhs) (forall-var rhs))
       (equal? (forall-body lhs) (forall-body rhs))))

(defmethod equal? ((lhs exists) (rhs exists))
  (and (equal? (exists-var lhs) (exists-var rhs))
       (equal? (exists-body lhs) (exists-body rhs))))

(defmethod equal? ((lhs predicate) (rhs predicate))
  (and (equal? (predicate-name lhs) (predicate-name rhs))
       (list-equal? (predicate-args lhs) (predicate-args rhs))))

(defmethod equal? ((lhs logical-constant) (rhs logical-constant))
  (eq (logical-constant-name lhs)
      (logical-constant-name rhs)))

(defun cons-distinct-vars (list new-vars)
  (reduce (lambda (coll x)
            (if (member x coll :key #'var-name)
                coll
                (cons x coll)))
          new-vars
          :initial-value list))

(defmethod vars ((fm formula))
  (typecase fm
    (implies (cons-distinct-vars (vars (implies-premise fm))
                                 (vars (implies-conclusion fm))))
    (iff (cons-distinct-vars (vars (iff-premise fm))
                             (vars (iff-conclusion fm))))
    (l-and (reduce #'cons-distinct-vars
                   (mapcar #'vars (l-and-conjuncts fm))))
    (l-or (reduce #'cons-distinct-vars
                  (mapcar #'vars (l-or-disjuncts fm))))
    (negation (vars (negation-argument fm)))
    (predicate (reduce #'cons-distinct-vars
                       (mapcar #'vars (predicate-args fm))))
    (exists (vars (exists-body fm)))
    (forall (vars (forall-body fm)))
    ;; logical constants have no variables
    (t nil)))

(defun free-vars (fm)
  "Returns the list of `VAR' objects which are not bound in FM."
  (declare (type formula fm))
  (typecase fm
    (implies (cons-distinct-vars (free-vars (implies-premise fm))
                                 (free-vars (implies-conclusion fm))))
    (iff (cons-distinct-vars (free-vars (iff-premise fm))
                             (free-vars (iff-conclusion fm))))
    (l-and (reduce #'cons-distinct-vars (mapcar #'free-vars (l-and-conjuncts fm))))
    (l-or (reduce #'cons-distinct-vars (mapcar #'free-vars (l-or-disjuncts fm))))
    (negation (free-vars (negation-argument fm)))
    (predicate (reduce #'cons-distinct-vars (mapcar #'vars (predicate-args fm))))
    (exists (remove-if (lambda (x)
                         (eq (var-name x)
                             (var-name (exists-var fm))))
                       (free-vars (exists-body fm))))
    (forall (remove-if (lambda (x)
                         (eq (var-name x)
                             (var-name (forall-var fm))))
                       (free-vars (forall-body fm))))
    ;; logical constants have no free variables
    (t nil)))

(defun generalize (fm)
  "Given a formula FM, universally quantify all free variables appearing in it."
  (declare (type formula fm))
  (reduce (lambda (form var)
            (forall var form))
          (free-vars fm)
          :initial-value fm))

;; TODO: consider how to rewrite `vars' and `free-vars' using a fold-formula
;; generic
(defgeneric fold-formula (fm f)
  (:documentation "Reduces a formula by subformulas, `f' expects (coll subformula) as its signature, producing a new list."))

(defmethod fold-formula ((fm implies) f)
  (reduce f (list (implies-premise fm)
                  (implies-conclusion fm))))

(defmethod fold-formula ((fm iff) f)
  (reduce f (list (iff-premise fm)
                  (iff-conclusion fm))))

(defmethod fold-formula ((fm l-or) f)
  (reduce f (l-or-disjuncts fm)))

(defmethod fold-formula ((fm l-and) f)
  (reduce f (l-and-conjuncts fm)))

(defmethod fold-formula ((fm negation) f)
  (fold-formula (negation-argument fm) f))

(defmethod fold-formula ((fm predicate) f)
  (funcall f fm nil))

(defmethod fold-formula ((fm exists) f)
  (funcall f fm nil))

(defmethod fold-formula ((fm forall) f)
  (funcall f fm nil))

;;;; Normal Forms.
;;;;
;;;; The less romantic aspect to theorem provers, we spend most of the time
;;;; transforming a formula into one normal form or another.
;;;;
;;;; Negation normal form "pulls in" negation to the atoms, replacing all
;;;; instances of "implies" with conjunction, disjunction, and negation.
;;;; It's the first step to prenix normal form, where we pull out all
;;;; the quantifiers to the start of the formula.
(defun not->nnf (not-p)
  "Helper function for (nnf (not p)), calls (not->nnf p)."
  (declare (type formula not-p))
  (typecase not-p
    (negation (nnf (negation-argument not-p)))
    (l-and (make-instance 'l-or
                          :disjuncts
                          (mapcar (lambda (clause)
                                    (nnf (negate clause)))
                                  (l-and-conjuncts not-p))))
    (l-or  (make-instance 'l-and
                          :conjuncts
                          (mapcar (lambda (clause)
                                    (nnf (negate clause)))
                                  (l-or-disjuncts not-p))))
    (implies (make-instance 'l-and
                            :conjuncts
                            (cons
                             (nnf (implies-premise not-p))
                             (nnf (negate (implies-conclusion not-p))))))
    (iff (lor (land
               (nnf (negate (iff-premise not-p)))
               (nnf (iff-conflusion not-p)))
              (land
               (nnf (iff-premise not-p))
               (nnf (negate (iff-conflusion not-p))))))
    (exists (make-instance 'forall
                           :var (exists-var not-p)
                           :body (nnf (negate (exists-body not-p)))))
    (forall
     (make-instance 'exists
                    :var (forall-var not-p)
                    :body (nnf (negate (forall-body not-p)))))
    ;; default to: we don't know what (not p) is, so return
    ;; (not (nnf p))
    (t (negate (nnf not-p)))
    ))

(defun nnf (p)
  "Handles positive formulas, delegates negations to `not->nnf'."
  (declare (type formula p))
  (typecase p
    (l-and (make-instance 'l-and
                          :conjuncts
                          (mapcar #'nnf (l-and-conjuncts p))))
    (l-or (make-instance 'l-or
                         :disjuncts
                         (mapcar #'nnf (l-or-disjuncts p))))
    (implies (lor (nnf (negate (implies-premise p)))
                  (nnf (implies-conclusion p))))
    (iff (lor (land (nnf (negate (iff-premise p)))
                    (nnf (negate (iff-conclusion p))))
              (land (nnf (iff-premise p))
                    (nnf (iff-conclusion p)))))
    (negation (not->nnf (negation-argument p)))
    (exists (make-instance 'exists
                           :var (exists-var p)
                           :body (nnf (exists-body p))))
    (forall (make-instance 'forall
                           :var (forall-var p)
                           :body (nnf (forall-body p))))
    (t p)))

(defun ->nnf (fm)
  (declare (type formula fm))
  (nnf fm))

(defun nnf? (fm)
  (declare (type formula fm))
  (typecase fm
    (l-and (every #'nnf? (l-and-conjuncts fm)))
    (l-or (every #'nnf? (l-or-disjuncts fm)))
    (exists (nnf? (exists-body fm)))
    (forall (nnf? (forall-body fm)))
    (negation (typep (negation-argument fm) 'predicate))
    (predicate t)
    (logical-constant t)))

;;; Prenex normal form.
;;;
;;; We pull out the quantifiers to make the formula look like:
;;; (quantifiers matrix) where there is no quantifier appearing in
;;; the subformula `matrix'.
;;;
;;; This requires substituting in a fresh variable to avoid accidental
;;; collisions.

;; Subst will replace all terms appearing in a formula according to the
;; provided REPLACEMENT-ALIST.
(defmethod term-subst ((self implies) replacement-alist &key (test #'equal?))
  (implies (term-subst (implies-premise self) replacement-alist :test test)
           (term-subst (implies-conclusion self) replacement-alist :test test)))

(defmethod term-subst ((self iff) replacement-alist &key (test #'equal?))
  (iff (term-subst (iff-premise self) replacement-alist :test test)
       (term-subst (iff-conclusion self) replacement-alist :test test)))

(defmethod term-subst ((self l-or) replacement-alist &key (test #'equal?))
  (make-instance
   'l-or
   :disjuncts (mapcar (lambda (clause)
                        (term-subst clause replacement-alist :test test))
                      (l-or-disjuncts self))))

(defmethod term-subst ((self l-and) replacement-alist &key (test #'equal?))
  (make-instance
   'l-and
   :conjuncts (mapcar (lambda (clause)
                        (term-subst clause replacement-alist :test test))
                      (l-and-conjuncts self))))

(defmethod term-subst ((self negation) replacement-alist &key (test #'equal?))
  (negate (term-subst (negation-argument self) replacement-alist :test test)))

(defmethod term-subst ((self predicate) replacement-alist &key (test #'equal?))
  (make-instance 'predicate
                 :name (predicate-name self)
                 :args (mapcar (lambda (tm)
                                 (term-subst tm replacement-alist :test test))
                               (predicate-args self))))

(defmethod term-subst ((self exists) replacement-alist &key (test #'equal?))
  (exists (term-subst (exists-var self) replacement-alist :test test)
          (term-subst (exists-body self) replacement-alist :test test)))

(defmethod term-subst ((self forall) replacement-alist &key (test #'equal?))
  (forall (term-subst (forall-var self) replacement-alist :test test)
          (term-subst (forall-body self) replacement-alist :test test)))

(defmethod term-subst ((self logical-constant) alist &key (test #'equal?))
  self)

(defmethod term-subst (self alist &key (test #'equal?))
  (format t "~% WTF term-subst found SELF = ~A" self)
  (format t "~%               typeof self = ~A" (type-of self))
  (format t "~%                     alist = ~A" alist))

;; Simplification by tautologies, removing un-used quantifiers, etc.
(defun prop-simplify (formula)
  (declare (type formula formula))
  (typecase formula
    (negation (cond
                ((verum? (negation-argument formula)) contradiction)
                ((contradiction? (negation-argument formula)) verum)
                ((typep (negation-argument formula)
                        'negation)
                 (negation-argument (negation-argument formula)))
                (t formula)))
    (l-and (cond
             ((some #'contradiction? (l-and-conjuncts formula))
              contradiction)
             (t (let ((results (remove-if #'verum?
                                          (l-and-conjuncts formula))))
                  (cond
                    ((null results) verum)
                    ((singleton? results) (car results))
                    (t (make-instance 'l-and
                                      :conjuncts results))
                    )))))
    (l-or (cond
            ((some #'verum? (l-or-disjuncts formula))
             verum)
            (t (let ((results (remove-if #'contradiction?
                                         (l-or-disjuncts formula))))
                 (cond
                   ((null results) contradiction)
                   ((singleton? results)
                    (car results))
                   (t (make-instance 'l-or
                                     :disjuncts results)))))))
    (implies (cond
               ((contradiction? (implies-premise formula)) verum)
               ((verum? (implies-premise formula)) (implies-conclusion formula))
               ((verum? (implies-conclusion formula)) verum)
               ((contradiction? (implies-conclusion formula))
                (negate (implies-conclusion formula)))
               (t formula)))
    (iff (cond
           ((verum? (iff-conclusion formula))
                       (iff-premise formula))
           ((verum? (iff-premise formula))
            (iff-conclusion formula))
           ((contradiction? (iff-premise formula))
            (negate (iff-conclusion formula)))
           ((contradiction? (iff-conclusion formula))
            (negate (iff-premise formula)))
           (t formula)
           ))
    (t formula)))

(defun remove-unused-quantifier (formula)
  (declare (type formula formula))
  (typecase formula
    (forall (if (member (forall-var formula)
                        (free-vars (forall-body formula))
                        :test #'equal?)
                formula
                (forall-body formula)))
    (exists (if (member (exists-var formula)
                        (free-vars (exists-body formula))
                        :test #'equal?)
                formula
                (exists-body formula)))
    (t (prop-simplify formula))))

(defun simplify (fm)
  (declare (type formula fm))
  (typecase fm
    (negation (remove-unused-quantifier (negate (simplify (negation-argument fm)))))
    (l-and (remove-unused-quantifier
            (let ((results (mapcar #'simplify (l-and-conjuncts fm))))
              (if (singleton? results)
                  (car results)
                  (make-instance 'l-and :conjuncts results)))))
    (l-or (remove-unused-quantifier
           (let ((results (mapcar #'simplify (l-or-disjuncts fm))))
             (if (singleton? results)
                 (car results)
                 (make-instance 'l-or :disjuncts results)))))
    (implies (remove-unused-quantifier
              (implies (simplify (implies-premise fm))
                       (simplify (implies-conclusion fm)))))
    (iff (remove-unused-quantifier
          (iff (simplify (iff-premise fm))
               (simplify (iff-conclusion fm)))))
    (forall (remove-unused-quantifier
             (forall (forall-var fm)
                     (simplify (forall-body fm)))))
    (exists (remove-unused-quantifier
             (exists (exists-var fm)
                     (simplify (exists-body fm)))))
    (t fm)
    ))

(defun simplify-example1 ()
  (labels ((make-prop (p) (make-instance 'predicate :name p :args nil)))
    (equal? (simplify (implies (implies verum (iff (make-prop 'x) contradiction))
                       (negate (lor (make-prop 'y)
                                    (land (make-prop 'z) contradiction)
                                    ))))
            (implies (negate (make-prop 'x))
                     (negate (make-prop 'y))))))

;; The basic strategy is to pull the quantifiers out "by one level", then
;; have `->prenex' recursively do this until we're in prenex normal form.
;;
;; We have formulas be in negation normal form, so the only binary connectives
;; are conjunction and disjunction. When any clause in a conjunction or disjunction
;; has a quantifier, we need to pull it out.
(defun var-variant (x)
  (declare (type (or symbol var) x))
  (var (gensym (symbol-name (if (typep x 'var)
                                (var-name x)
                                x)))))


(defgeneric has-quantified-clause? (fm))

(defmethod has-quantified-clause? (fm))

(defmethod has-quantified-clause? ((fm forall))
  t)

(defmethod has-quantified-clause? ((fm exists))
  t)

(defmethod has-quantified-clause? ((fm l-or))
  (some (lambda (clause)
          (has-quantified-clause? clause))
        (l-or-disjuncts fm)))

(defmethod has-quantified-clause? ((fm l-and))
  (some (lambda (clause)
          (has-quantified-clause? clause))
        (l-and-conjuncts fm)))

(defun pull-quantifiers (fm)
  (declare (type formula fm))
  (assert (nnf? fm))
  (labels ((pull-quantifiers-for-clauses (clauses connective fvars)
             (funcall (lambda (clauses-and-quants)
                        (funcall (cdr clauses-and-quants)
                                 (pull-quantifiers-inner
                                  (apply connective (car clauses-and-quants)))))
                      (reduce (lambda (clause clauses-and-quants) 
                                (let* ((processed-clauses (car clauses-and-quants))
                                       (quants (cdr clauses-and-quants)))
                                  (typecase clause
                                    (forall (let ((fresh-var (if (member (forall-var clause) fvars :test #'equal?)
                                                                 (var-variant (forall-var clause))
                                                                 (forall-var clause))))
                                              (cons (cons (term-subst (forall-body clause)
                                                           (acons (forall-var clause)
                                                                  fresh-var
                                                                  nil))
                                                          processed-clauses)
                                                    (lambda (x)
                                                      (forall fresh-var (funcall quants x))))))
                                    (exists (let ((fresh-var (if (member (exists-var clause) fvars :test #'equal?)
                                                                 (var-variant (exists-var clause))
                                                                 (exists-var clause))))
                                              (cons (cons (term-subst (exists-body clause)
                                                                      (acons (exists-var clause)
                                                                             fresh-var
                                                                             nil))
                                                          processed-clauses)
                                                    (lambda (x)
                                                      (exists fresh-var (funcall quants x))))))
                                    (t (cons (cons clause processed-clauses) quants)))
                                  ))
                              clauses
                              :initial-value '(nil . identity)
                              :from-end t)))
           (pull-quantifiers-inner (form)
             (declare (type formula form))
             (typecase form
               ;; TODO: handle (land (forall x (p x)) (forall y (q y)))
               ;;     => (forall z (land (p z) (q z)))
               (l-and (if (has-quantified-clause? form)
                          (pull-quantifiers-for-clauses (l-and-conjuncts form) #'land (free-vars form))
                          form))
               ;; TODO: handle (lor (exists x (p x)) (exists y (q y)))
               ;;     => (exists z (lor (p z) (q z)))
               (l-or (if (has-quantified-clause? form)
                         (pull-quantifiers-for-clauses (l-or-disjuncts form) #'lor (free-vars form))
                         form))
               (t form)
               )))
    (pull-quantifiers-inner fm)
    ))

(defun nnf->prenex (fm)
  (declare (type formula fm))
  ;; (assert (nnf? fm))
  (typecase fm
    (forall (forall (forall-var fm) (nnf->prenex (forall-body fm))))
    (exists (exists (exists-var fm) (nnf->prenex (exists-body fm))))
    (l-and (pull-quantifiers (make-instance 'l-and
                                            :conjuncts (mapcar #'nnf->prenex (l-and-conjuncts fm)))))
    (l-or (pull-quantifiers (make-instance 'l-or
                                           :disjuncts (mapcar #'nnf->prenex (l-or-disjuncts fm)))))
    (t fm)))

(defun prenex-normal-form (fm)
  "Simplifies and transforms a formula FM, making it in prenex normal form."
  (nnf->prenex (->nnf (simplify fm))))

(defun pnf-ex1 ()
  (labels ((p (x)
             (make-instance 'predicate
                            :name :P
                            :args (list (var x))))
           (q (x)
             (make-instance 'predicate
                            :name :Q
                            :args (list (var x))))
           (r (x)
             (make-instance 'predicate
                            :name :R
                            :args (list (var x))))
           )
    (prenex-normal-form
     (implies (forall 'x (lor (p 'x) (r 'y)))
              (lor (exists 'y (exists 'z (negate (q 'y))))
                   (negate (exists 'z (land (p 'z) (q 'z)))))
              ))))

