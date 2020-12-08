(defpackage #:cl-aim.utils
  (:use #:cl)
  (:export equal? list-equal? singleton? flatten-if))
(in-package #:cl-aim.utils)

(defun singleton? (coll)
  (and (consp coll)
       (endp (cdr coll))))

(defgeneric equal? (lhs rhs))

(defmethod equal? (lhs rhs)
  (equalp lhs rhs))

(defmethod equal? ((lhs symbol) (rhs symbol))
  (eq lhs rhs))

(defmethod equal? ((lhs number) (rhs number))
  (= lhs rhs))

(defmethod equal? ((lhs cons) (rhs cons))
  (and (equal? (car lhs) (car rhs))
       (equal? (cdr lhs) (cdr rhs))))

(defun list-equal? (lhs rhs)
  (cond
    ((null lhs) (null rhs))
    ((equal? (car lhs) (car rhs)) (list-equal? (cdr lhs) (cdr rhs)))
    (t nil)))

(defun flatten-if (condition? coll &key (test #'equal?) (transform #'identity))
  (reduce (lambda (item list)
            (if (null item)
                list
                (if (funcall condition? item)
                    (append (funcall transform item) list)
                    (cons item list))))
          coll
          :initial-value nil
          :from-end t))
