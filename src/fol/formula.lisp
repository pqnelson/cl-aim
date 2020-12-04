(defpackage #:cl-aim.fol.formula
  (:use #:cl #:cl-aim.utils)
  (:import-from #:cl-aim.fol.term vars var term fn var-name))
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

(defmethod print-object ((object implies) stream)
  (format stream "(#implies ~A ~A)" (implies-premise object)
          (implies-conclusion object)))

(defclass l-or (formula)
  ((disjuncts :initarg :disjuncts
              :accessor l-or-disjuncts
              :type (list formula))))

(defmethod print-object ((object l-or) stream)
  (format stream "(#or ~A)" (l-or-disjuncts object)))

(defun lor (&rest disjuncts)
  (make-instance 'l-or :disjuncts disjuncts))

(defclass l-and (formula)
  ((conjuncts :initarg :conjuncts
              :accessor l-and-conjuncts
              :type (list formula))))

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

(unless (boundp 'contradiction)
  (defconstant contradiction (make-instance 'logical-constant :name 'contradiction)
    "The 'false' constant."))

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

(defclass predicate (formula)
  ((name :initarg :name
         :accessor predicate-name)
   (args :initarg :args
         :accessor predicate-args
         :type (list cl-aim.fol.term:term))))

(defmethod print-object ((object predicate) stream)
  (format stream "#pred(~A ~A)" (predicate-name object)
          (predicate-args object)))

;; BUG: this doesn't work, splitting it out into multiple defmethods doesn't
;; work either. I can't adequately do unit testing until I figure this out...
(defmethod equal? ((lhs formula) (rhs formula))
  (when (typep rhs (type-of lhs))
    (typecase lhs
      (implies (and (equal? (implies-premise lhs) (implies-premise rhs))
                    (equal? (implies-conclusion lhs) (implies-conclusion rhs))))
      (iff (and (equal? (iff-premise lhs) (iff-premise rhs))
                (equal? (iff-conclusion lhs) (iff-conclusion rhs))))
      (l-or (every equal?
                   (l-or-disjuncts lhs)
                   (l-or-disjuncts rhs)))
      (l-and (every equal?
                    (l-and-conjuncts lhs)
                    (l-and-conjuncts rhs)))
      (negation (equal? (negation-argument lhs) (negation-argument rhs)))
      (forall (and (equal? (forall-var lhs) (forall-var rhs))
                   (equal? (forall-body lhs) (forall-body rhs))))
      (exists (and (equal? (exists-var lhs) (exists-var rhs))
                   (equal? (exists-body lhs) (exists-body rhs))))
      (predicate (and (equal? (predicate-name lhs) (predicate-name rhs))
                      (every equal? (predicate-args lhs) (predicate-args rhs))))
      (logical-constant (eq (logical-constant-name lhs)
                            (logical-constant-name rhs)))
      )))

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
            (make-instance 'forall :var var :body form))
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

(defun nnf-ex0 ()
  (labels ((p (x) (make-instance 'predicate
                                 :name 'P
                                 :args (list (var x)))))
    (->nnf
     (negate (make-instance 'exists
                            :var (var 'x)
                            :body (p 'x))))))


(defun nnf-ex2 ()
  (labels ((p (x) (make-instance 'predicate
                                 :name 'P
                                 :args (list (var x)))))
    (->nnf
     (negate (make-instance 'forall
                            :var (var 'x)
                            :body (p 'x))))))

(defun nnf-ex1 ()
  (labels ((p (x) (make-instance 'predicate
                                 :name 'P
                                 :args (list (var x))))
           (q (x) (make-instance 'predicate
                                 :name 'Q
                                 :args (list (var x)))))
    (->nnf
     (make-instance
      'implies
      :premise (make-instance 'forall
                              :var (var 'x)
                              :body (p 'x))
      :conclusion (make-instance 'forall
                                 :var (var 'y)
                                 :body (q 'y))))))

;; (defun nnf-ex2 ()
;;   (labels ((p (x) (make-instance 'predicate
;;                                  :name 'P
;;                                  :args (list (var x))))
;;            (q (x) (make-instance 'predicate
;;                                  :name 'Q
;;                                  :args (list (var x)))))
;;     (->nnf
;;      (make-instance
;;       'implies
;;       :premise (make-instance 'exists
;;                               :var (var 'x)
;;                               :body (p 'x))
;;       :conclusion (make-instance 'iff
;;                                  :premise (make-instance
;;                                            'exists
;;                                            :var (var 'y)
;;                                            :body (q 'y))
;;                                  :conclusion (make-instance
;;                                               'exists
;;                                               :var (var 'z)
;;                                               :body (land
;;                                                      (p 'z)
;;                                                      (q 'z))))
;;       :conclusion (make-instance 'forall
;;                                  :var (var 'y)
;;                                  :body (q 'y))))))

(defun nnf-example ()
  (labels ((p (x) (make-instance 'predicate
                                 :name 'P
                                 :args (list (var x))))
           (q (x) (make-instance 'predicate
                                 :name 'Q
                                 :args (list (var x)))))
    (->nnf
     (make-instance 'implies
                    :premise (make-instance 'forall
                                            :var (var 'x)
                                            :body (p 'x))
                    :conclusion (make-instance 'iff
                                               :premise (make-instance
                                                         'exists
                                                         :var (var 'y)
                                                         :body (q 'y))
                                               :conclusion (make-instance
                                                            'exists
                                                            :var (var 'z)
                                                            :body (land
                                                                   (p 'z)
                                                                   (q 'z)))))))
  )
