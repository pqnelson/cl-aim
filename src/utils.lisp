(defpackage #:cl-aim.utils
  (:use #:cl)
  (:export equal?))
(in-package #:cl-aim.utils)

(defgeneric equal? (lhs rhs))

(defmethod equal? (lhs rhs)
  (equalp lhs rhs))

(defmethod equal? ((lhs symbol) (rhs symbol))
  (eq lhs rhs))

(defmethod equal? ((lhs number) (rhs number))
  (= lhs rhs))
