(defpackage #:cl-aim.fol.term
  (:use :cl :cl-aim.utils)  
  (:export var-name fn fn? fn-name fn-args
           var term
           vars
           arity
           equal?
           term-subst
           functions
           occurs-in?))
(in-package #:cl-aim.fol.term)

(defclass term ()
  ())

(defclass var (term)
  ((name :accessor var-name
         :initarg :name)))

(defmethod equal? ((lhs var) (rhs var))
  (equal? (var-name lhs) (var-name rhs)))

(defparameter *debug?* nil)

(defmethod print-object ((object var) stream)
  (format stream (if *debug?* "(#var ~A)" "~A") (var-name object)))

(defun var (x)
  (if (typep x 'var)
      x
      (make-instance 'var :name x)))

(defclass fn (term)
  ((name :accessor fn-name
         :initarg :name)
   (args :accessor fn-args
         :initarg :args
         :type (cons term))))

(defun fn (f args)
  (make-instance 'fn
                 :name f
                 :args args))

(defun fn? (x)
  (typep x 'fn))

(defmethod equal? ((lhs fn) (rhs fn))
  (and (equal? (fn-name lhs) (fn-name rhs))
       (list-equal? (fn-args lhs) (fn-args rhs))))

(defmethod print-object ((object fn) stream)
  (format stream "#fn(~A ~A)" (fn-name object) (fn-args object)))

(defgeneric arity (f))

(defmethod arity ((f fn))
  (length (fn-args f)))

;;;; Free and bound variables occurring in a term.
(defgeneric vars (x)
  (:documentation "Return all the VAR instances in the term."))

(defmethod vars ((self var))
  (list self))

(defmethod vars ((self fn))
  (when (plusp (arity self))
    (remove-duplicates (mapcan #'vars (fn-args self))
                       :key #'var-name)))

;;;; Term substitution.
(defgeneric term-subst (self replacement-alist &key test ;; (test #'equal?)
                                               ))

(defmethod term-subst ((self var) replacement-alist &key (test #'equal?))
  (let ((replacement (assoc self replacement-alist :test test)))
    (if replacement
        (cdr replacement)
        self)))

(defmethod term-subst ((self fn) replacement-alist &key (test #'equal?))
  (fn (fn-name self)
      (mapcar (lambda (arg)
                (term-subst arg replacement-alist :test test))
              (fn-args self))))

;;;; Functions appearing in an expression.
(defgeneric functions (self)
  (:documentation "Returns a list of symbols used as function names appearing in expression"))

(defmethod functions ((self var))
  nil)

(defmethod functions ((self fn))
  (let ((results (remove-duplicates (mapcan #'functions (fn-args self))
                                    :test #'equal?)))
    (if (member (fn-name self) results :test #'equal?)
        results
        (cons (fn-name self) results))))

;;; A helper function to check if a subexpression occurs in an expression
(defgeneric occurs-in? (sub expr))

(defmethod occurs-in? (sub (expr var))
  (equal? sub expr))

(defmethod occurs-in? (sub (expr fn))
  (or (equal? expr)
      (some #'(lambda (e) (occurs-in? sub e))
            (fn-args expr))))
