(defpackage #:cl-aim.fol.term
  (:use :cl :cl-aim.utils)
  (:export var-name fn fn-name fn-args
           var term
           vars
           arity
           equal?))
(in-package #:cl-aim.fol.term)

(defclass term ()
  ())

(defclass var (term)
  ((name :accessor var-name
         :initarg :name)))

(defmethod equal? ((lhs var) (rhs var))
  (equal? (var-name lhs) (var-name rhs)))

(defmethod print-object ((object var) stream)
  (format stream "~A" (var-name object)))

(defun var (x)
  (make-instance 'var :name x))

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

(defmethod equal? ((lhs fn) (rhs fn))
  (and (equal? (fn-name lhs) (fn-name rhs))
       (list-equal? (fn-args lhs) (fn-args rhs))))

(defmethod print-object ((object fn) stream)
  (format stream "#fn(~A ~A)" (fn-name object) (fn-args object)))

(defgeneric arity (f))

(defmethod arity ((f fn))
  (length (fn-args f)))

(defgeneric vars (x)
  (:documentation "Return all the VAR instances in the term."))

(defmethod vars ((self var))
  (list self))

(defmethod vars ((self fn))
  (when (plusp (arity self))
    (remove-duplicates (mapcan #'vars (fn-args self))
                       :key #'var-name)))
