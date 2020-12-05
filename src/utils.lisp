(defpackage #:cl-aim.utils
  (:use #:cl)
  (:export equal? list-equal?))
(in-package #:cl-aim.utils)

(defgeneric equal? (lhs rhs))

(defmethod equal? (lhs rhs)
  (equalp lhs rhs))

(defmethod equal? ((lhs symbol) (rhs symbol))
  (eq lhs rhs))

(defmethod equal? ((lhs number) (rhs number))
  (= lhs rhs))

(defun list-equal? (lhs rhs)
  (cond
    ((null lhs) (null rhs))
    ((equal? (car lhs) (car rhs)) (list-equal? (cdr lhs) (cdr rhs)))
    (t nil)))
