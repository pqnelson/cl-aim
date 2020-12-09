(defpackage #:cl-aim.fol.formula
  (:use #:cl #:cl-aim.utils)
  (:shadowing-import-from #:cl-aim.fol.term occurs-in?)
  (:import-from #:cl-aim.fol.term vars var term fn var-name term-subst functions)
  (:export formula iff iff-premise iff-conclusion iff?
           implies implies-premise implies-conclusion implies?
           l-and land l-and l-and-conjuncts land?
           l-or lor l-or-disjuncts lor?
           negation l-neg negation-argument negation?
           predicate predicate? predicate-name predicate-args
           prop equals forall forall? exists exists-var exists-body
           logical-constant verum-type verum
           contradiction contradiction? contradiction-type
           negative-prop-literal? neg-prop-lit pos-prop-lit prop-literal
           vars free-vars simplify
           equal? occurs-in? free-in?
           ->nnf term-subst
           pull-quantifiers skolemize))
(in-package #:cl-aim.fol.formula)
;; NOTE: we experience a performance hit, I think, by making `->nnf'
;;       and prenex-normal-form produce new formulas rather than mutating
;;       in place.

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

(defun implies? (x) (typep x 'implies))

(defmethod print-object ((object implies) stream)
  (format stream "(implies ~A ~A)" (implies-premise object)
          (implies-conclusion object)))

(defclass l-or (formula)
  ((disjuncts :initarg :disjuncts
              :accessor l-or-disjuncts
              :type (cons formula))))

(defmethod print-object ((object l-or) stream)
  (format stream "(lor ~{~A~^ ~})" (l-or-disjuncts object)))

(defun lor? (x) (typep x 'l-or))

(defun lor (&rest disjuncts)
  (make-instance
   'l-or
   :disjuncts (flatten-if #'lor? disjuncts :transform #'l-or-disjuncts)))

(defclass l-and (formula)
  ((conjuncts :initarg :conjuncts
              :accessor l-and-conjuncts
              :type (cons formula))))

(defun land? (x) (typep x 'l-and))

(defmethod print-object ((object l-and) stream)
  (format stream "(land ~{~A~^ ~})" (l-and-conjuncts object)))

(defun land (&rest conjuncts)
  (if (singleton? conjuncts)
      (car conjuncts)
      (make-instance
       'l-and
       :conjuncts (flatten-if #'land? conjuncts
                              :transform #'l-and-conjuncts))))

(defclass negation (formula)
  ((argument :initarg :formula
             :accessor negation-argument
             :type formula)))

(defmethod print-object ((object negation) stream)
  (format stream "(#not ~A)" (negation-argument object)))

(defun negation? (x) (typep x 'negation))

(defun l-neg (fm)
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
  (format stream "(iff ~A ~A)" (iff-premise object)
          (iff-conclusion object)))

(defun iff? (x) (typep x 'iff))

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

(deftype verum-type ()
  `(and logical-constant
        (satisfies verum?)))

(unless (boundp 'contradiction)
  (defconstant contradiction (make-instance 'logical-constant :name 'contradiction)
    "The 'false' constant."))

(defun contradiction? (x)
  (eq contradiction x))

(deftype contradiction-type ()
  `(and logical-constant
        (satisfies contradiction?)))

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

(defun forall? (x) (typep x 'forall))

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

(defun exists? (x) (typep x 'exists))

(defclass predicate (formula)
  ((name :initarg :name
         :accessor predicate-name)
   (args :initarg :args
         :accessor predicate-args
         :initform nil
         :type (or null (cons cl-aim.fol.term:term)))))

(defmethod print-object ((object predicate) stream)
  (format stream "#pred(~A~{ ~A~^ ~})" (predicate-name object)
          (predicate-args object)))

(defun predicate? (x) (typep x 'predicate))

(defun predicate (p args)
  (make-instance 'predicate
                 :name p
                 :args args))

(defun negative-prop-literal? (x)
  (and (implies? x)
       (contradiction? (implies-conclusion x))
       (or (typep x 'predicate)
           (typep x 'forall))))

(deftype neg-prop-lit ()
  `(and implies
        (satisfies negative-prop-literal?)))

(deftype pos-prop-lit ()
  `(or predicate
       forall))

(deftype prop-literal ()
  `(or pos-prop-lit
       neg-prop-lit))

(defun prop (p)
  (declare (type symbol p))
  (make-instance 'predicate
                 :name p
                 :args nil))

(defun equals (lhs rhs)
  "Make a formula asserting equality of terms."
  (declare (type term lhs rhs))
  (make-instance 'predicate
                 :name '=
                 :args (list lhs rhs)))

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

;;; test if a subexpression occurs anywhere in an expression
(defmethod occurs-in? (sub (expr implies))
  (or (equal? sub expr)
      (occurs-in? sub (implies-premise expr))
      (occurs-in? sub (implies-conclusion expr))))

(defmethod occurs-in? (sub (expr iff))
  (or (equal? sub expr)
      (occurs-in? sub (iff-premise expr))
      (occurs-in? sub (iff-conclusion expr))))

(defmethod occurs-in? (sub (expr negation))
  (or (equal? sub expr)
      (occurs-in? (negation-argument expr))))

(defmethod occurs-in? (sub (expr l-or))
  (or (equal? sub expr)
      (some #'(lambda (e) (occurs-in? sub e))
            (l-or-disjuncts expr))))

(defmethod occurs-in? (sub (expr l-and))
  (or (equal? sub expr)
      (some #'(lambda (e) (occurs-in? sub e))
            (l-and-conjuncts expr))))

(defmethod occurs-in? (sub (expr logical-constant))
  (equal? sub expr))

(defmethod occurs-in? (sub (expr predicate))
  (or (equal? sub expr)
      (some #'(lambda (e) (occurs-in? sub e))
            (predicate-args expr))))

;;; check if a term is free in a formula
(defgeneric free-in? (tm fm))

(defmethod free-in? ((tm term) (fm implies))
  (or (free-in? tm (implies-premise fm))
      (free-in? tm (implies-conclusion fm))))

(defmethod free-in? ((tm term) (fm iff))
  (or (free-in? tm (iff-premise fm))
      (free-in? tm (iff-conclusion fm))))

(defmethod free-in? ((tm term) (fm l-and))
  (some #'(lambda (clause)
            (free-in? tm clause))
        (l-and-conjuncts fm)))

(defmethod free-in? ((tm term) (fm l-or))
  (some #'(lambda (clause)
            (free-in? tm clause))
        (l-or-disjuncts fm)))

(defmethod free-in? ((tm term) (fm negation))
  (free-in? tm (negation-argument fm)))

(defmethod free-in? ((tm term) (fm predicate))
  (some #'(lambda (arg)
            (occurs-in? tm arg))
        (predicate-args fm)))

(defmethod free-in? ((tm term) (fm exists))
  (unless (occurs-in? (exists-var fm) tm)
    (occurs-in? tm (exists-body fm))))

(defmethod free-in? ((tm term) (fm forall))
  (unless (occurs-in? (forall-var fm) tm)
    (occurs-in? tm (forall-body fm))))

(defmethod free-in? ((tm term) (fm formula))
  nil)

;;; all variables occurring in a formula
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
(defun reduce-over-atoms (f fm initial-value)
  (declare (type formula fm)
           (type function f))
  (typecase fm
    (predicate (funcall f fm initial-value))
    (negation (reduce-over-atoms f (negation-body fm) initial-value))
    (implies (reduce-over-atoms f
                                (implies-premise fm)
                                (reduce-over-atoms f
                                                   (implies-conclusion fm)
                                                   initial-value)))
    (iff (reduce-over-atoms f
                            (iff-premise fm)
                            (reduce-over-atoms f
                                               (iff-conclusion fm)
                                               initial-value)))
    (l-and (reduce (lambda (clause current-val)
                     (reduce-over-atoms f clause current-val))
                   (l-and-conjuncts fm)
                   :initial-value initial-value))
    (l-or (reduce (lambda (clause current-val)
                    (reduce-over-atoms f clause current-val))
                  (l-or-disjuncts fm)
                  :initial-value initial-value))
    (forall (reduce-over-atoms f (forall-body fm) initial-value))
    (exists (reduce-over-atoms f (exists-body fm) initial-value))
    (t initial-value)))

(defun map-atoms (f fm)
  (declare (type formula fm)
           (type (function (formula *) *) f))
  (typecase fm
    (predicate (f fm))
    (negation (l-neg (map-atoms f (negation-body fm))))
    (l-and (make-instance 'l-and
                          :conjuncts (mapcar (lambda (clause)
                                               (map-atoms f clause))
                                             (l-and-conjuncts fm))))
    (l-or (make-instance 'l-or
                          :disjuncts (mapcar (lambda (clause)
                                               (map-atoms f clause))
                                             (l-or-disjuncts fm))))
    (implies (implies (map-atoms f (implies-premise fm))
                      (map-atoms f (implies-conclusion fm))))
    (iff (iff (map-atoms f (iff-premise fm))
              (map-atoms f (iff-conclusion fm))))
    (forall (forall (forall-var fm)
                    (map-atoms f (forall-body fm))))
    (exists (exists (exists-var fm)
                    (map-atoms f (exists-body fm))))
    (t fm)
    ))


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
                                    (nnf (l-neg clause)))
                                  (l-and-conjuncts not-p))))
    (l-or  (make-instance 'l-and
                          :conjuncts
                          (mapcar (lambda (clause)
                                    (nnf (l-neg clause)))
                                  (l-or-disjuncts not-p))))
    (implies (make-instance 'l-and
                            :conjuncts
                            (cons
                             (nnf (implies-premise not-p))
                             (nnf (l-neg (implies-conclusion not-p))))))
    (iff (lor (land
               (nnf (l-neg (iff-premise not-p)))
               (nnf (iff-conflusion not-p)))
              (land
               (nnf (iff-premise not-p))
               (nnf (l-neg (iff-conflusion not-p))))))
    (exists (make-instance 'forall
                           :var (exists-var not-p)
                           :body (nnf (l-neg (exists-body not-p)))))
    (forall
     (make-instance 'exists
                    :var (forall-var not-p)
                    :body (nnf (l-neg (forall-body not-p)))))
    ;; default to: we don't know what (not p) is, so return
    ;; (not (nnf p))
    (t (l-neg (nnf not-p)))
    ))

(defun nnf (p)
  "Handles positive formulas, delegates negations to `not->nnf'."
  (declare (type formula p))
  (typecase p
    (l-and (make-instance 'l-and
                          :conjuncts
                          (mapcan (lambda (clause)
                                    (if (land? clause)
                                        (l-and-conjuncts clause)
                                        (list clause)))
                                  (mapcar #'nnf (l-and-conjuncts p)))))
    (l-or (make-instance 'l-or
                         :disjuncts
                         (mapcan (lambda (clause)
                                   (if (lor? clause)
                                       (l-or-disjuncts clause)
                                       (list clause)))
                                 (mapcar #'nnf (l-or-disjuncts p)))))
    (implies (let ((premise (nnf (l-neg (implies-premise p))))
                   (conclusion (nnf (implies-conclusion p))))
               (cond
                 ((lor? premise)
                  (cond ((lor? conclusion)
                         (progn
                           (setf (l-or-disjuncts premise)
                                 (append (l-or-disjuncts premise)
                                         (l-or-disjuncts conclusion)))
                           premise))
                        ((or (exists? conclusion)
                             (forall? conclusion)
                             (predicate? conclusion))
                         (progn
                           (setf (l-or-disjuncts premise)
                                 (append (l-or-disjuncts premise)
                                         (list conclusion)))
                           premise))
                        (t (lor premise conclusion))))
                 ((lor? conclusion)
                  (cond ((or (exists? premise)
                             (forall? premise)
                             (predicate? premise))
                         (progn
                           (setf (l-or-disjuncts conclusion)
                                 (cons premise
                                       (l-or-disjuncts conclusion)))
                           conclusion))
                        (t (lor premise conclusion))))
                 (t (lor premise conclusion)))))
    (iff (lor (land (nnf (l-neg (iff-premise p)))
                    (nnf (l-neg (iff-conclusion p))))
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
    (negation (predicate? (negation-argument fm)))
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
  (l-neg (term-subst (negation-argument self) replacement-alist :test test)))

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
                ((negation? (negation-argument formula))
                 (negation-argument (negation-argument formula)))
                (t formula)))
    ;; TODO: consider "flattening" nested (#and a (#and b c) d)
    ;;       to just (#and a b c d)
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
    ;; TODO: consider "flattening" nested (#or a (#or b c) d)
    ;;       to just (#or a b c d)
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
                (l-neg (implies-conclusion formula)))
               (t formula)))
    (iff (cond
           ((verum? (iff-conclusion formula))
                       (iff-premise formula))
           ((verum? (iff-premise formula))
            (iff-conclusion formula))
           ((contradiction? (iff-premise formula))
            (l-neg (iff-conclusion formula)))
           ((contradiction? (iff-conclusion formula))
            (l-neg (iff-premise formula)))
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
    (negation (remove-unused-quantifier (l-neg (simplify (negation-argument fm)))))
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


(defun pull-exists-before-lor (fm)
  "Peels off one layer of existential quantifiers in clauses in a disjunction."
  (declare (type (or exists l-or) fm))
  ;; change (or (exists x1 (p1 x1)) ... (exists x-n (p-n x-n)))
  ;; into (exists z (or (p1 z) ... (p-n z)))

  ;; change (or (exists x (or (p x) (q x))) (exists y (r y)))
  ;;   into (exists z (or (p z) (q z) (r z)))
  fm
  )

(defun bound-vars (fm)
  "Returns all bound variables in a formula."
  (declare (type formula fm))
  (typecase fm
    (implies (concatenate 'list
                          (bound-vars (implies-premise fm))
                          (bound-vars (implies-conclusion fm))))
    (iff (concatenate 'list
                      (bound-vars (iff-premise fm))
                      (bound-vars (iff-conclusion fm))))
    (l-or (mapcan #'bound-vars (l-or-disjuncts fm)))
    (l-and (mapcan #'bound-vars (l-and-conjuncts fm)))
    (negation (bound-vars (negation-argument fm)))
    (forall (let ((results (bound-vars (forall-body fm))))
              (if (member (forall-var fm) results :test #'equal?)
                  results
                  (cons (exists-var fm) results))))
    (exists (let ((results (bound-vars (exists-body fm))))
              (if (member (exists-var fm) results :test #'equal?)
                  results
                  (cons (exists-var fm) results))))
    (t nil)
    ))

(defun pull-forall-before-land (fm)
  "Peels off one layer of universal quantifiers in clauses in a conjunction."
  (declare (type (or forall l-and) fm))
  ;; change (and (forall x1 (p1 x1)) ... (forall x-n (p-n x-n)))
  ;; into (forall z (and (p1 z) ... (p-n z)))

  ;; change (and (forall x (and (p x) (q x))) (forall y (r y)))
  ;;   into (forall z (and (p z) (q z) (r z)))
  fm
  )

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
               (l-and (if (has-quantified-clause? form)
                          (let ((contracted (pull-forall-before-land form)))
                            (if (equal? contracted form)
                                (pull-quantifiers-for-clauses (l-and-conjuncts contracted) #'land (free-vars contracted))
                                (let ((body (forall-body contracted)))
                                  (setf (forall-body contracted)
                                        (pull-quantifiers-inner body))
                                  contracted)))
                          form))
               (l-or (if (has-quantified-clause? form)
                         (let ((contracted (pull-exists-before-lor form)))
                           (if (equal? contracted form)
                               (pull-quantifiers-for-clauses (l-or-disjuncts contracted) #'lor (free-vars contracted))
                               (let ((body (exists-body contracted)))
                                 (setf (exists-body contracted)
                                       (pull-quantifiers-inner body))
                                 contracted)))
                         form))
               (t form)
               )))
    (pull-quantifiers-inner fm)
    ))

(defun nnf->prenex (fm)
  (declare (type formula fm))
  (assert (nnf? fm))
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
    (->nnf ;; prenex-normal-form
     (simplify
      (implies (forall 'x (lor (p 'x) (r 'y)))
              (lor (exists 'y (exists 'z (l-neg (q 'y))))
                   (l-neg (exists 'z (land (p 'z) (q 'z)))))
              )))))

;;;; Skolemization and Herbrandization.
;;;; 
;;;; We can skolemize formulas in prenex normal form, i.e., replace
;;;; all instances of existantially quantified variables with
;;;; functions (or constants). Schematically the formula
;;;; 
;;;;     (forall (x_1 .. x_m) (exists y) (fm x_1 .. x_m y))
;;;; 
;;;; becomes
;;;; 
;;;;     (forall (x_1 .. x_m) (fm x_1 .. x_m (skolem-fn y x_1 .. x_m)))
;;;; 
;;;; where `skolem-fn' is a fresh function named `y' which depends on
;;;; arguments `x_1', ..., `x_m'.
;;;; 

(defmethod functions ((self formula))
  (remove-duplicates
   (reduce-over-atoms (lambda (pred fns)
                        (append
                         fns
                         (mapcan #'functions (predicate-args pred))))
                      self
                      nil)
   :test #'equal?))

(defun skolem-symbol (name)
  (intern name 'cl-aim.fol.formula))

(defun skolem (fm fns)
  "Produces a pair (skolemized-formula . fn-symbols-in-use)"
  (declare (type formula fm))
  (labels ((skolem-binary (clauses fns%)
             (reduce (lambda (clause current-vals)
                       (let* ((current-clauses (car current-vals))
                              (current-fns (cdr current-vals))
                              (results (skolem clause current-fns)))
                         (cons (cons (car results) current-clauses)
                               (cdr results))))
                     clauses
                     :initial-value (cons nil fns%)
                     :from-end t
                     )))
  (typecase fm
    (exists (let* ((fvs (remove-duplicates (free-vars fm) :test #'equal?))
                   (f0 (skolem-symbol
                        (concatenate 'string
                                     (if (null fvs)
                                         "c_"
                                         "f_")
                                     (symbol-name (var-name (exists-var fm))))))
                   (f (if (member f0 fns :test #'equal?)
                          (gensym (symbol-name f0))
                          f0))
                   (skolem-f (fn f (remove-duplicates
                                    (mapcar #'var fvs)
                                    :test #'equal?))))
              (skolem (term-subst (exists-body fm)
                                  (acons (exists-var fm) skolem-f nil)
                                  :test #'equal?)
                      (if (member f fns :test #'equal?)
                          fns
                          (cons f fns)))))
    (forall (let* ((results (skolem (forall-body fm) fns))
                   )
              (cons (forall (forall-var fm) (car results))
                    (cdr results))))
    (l-and (let ((clauses-and-fns (skolem-binary
                                   (l-and-conjuncts fm)
                                   fns)))
             (cons (make-instance 'l-and
                                  :conjuncts (car clauses-and-fns))
                   (cdr clauses-and-fns))))
    (l-or (let ((clauses-and-fns (skolem-binary
                                  (l-or-disjuncts fm)
                                  fns)))
            (cons (make-instance 'l-or :disjuncts (car clauses-and-fns))
                  (cdr clauses-and-fns))))
    (t (list fm fns)))))

(defgeneric specialize (fm)
  (:documentation "Removes all leading `forall' quantifiers in formula.

Useful for giving an equisatisfiable formula with no explicit quantification.
This comes in handy for a few satisfiability algorithms."))

(defmethod specialize ((fm forall))
  (specialize (forall-body fm)))

(defmethod specialize ((fm formula))
  fm)

(defun skolemize (fm)
  (declare (type formula fm))
  (let ((nnf-skolemized (car (skolem
                              (->nnf (simplify fm))
                              (functions fm)))))
    (specialize (nnf->prenex nnf-skolemized))))


