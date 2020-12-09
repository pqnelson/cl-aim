(defpackage #:cl-aim.utils
  (:use #:cl)
  (:export equal? list-equal? singleton? flatten-if partition-by))
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

(defun partition (n coll)
  (declare (type integer n)
           (type (or cons nil) coll))
  (let ((results nil))
    (labels ((partition-inner (k lst)
               (if (and (plusp k)
                        (not (endp lst)))
                   (progn
                     (push (car lst) results)
                     (partition-inner (1- k) (cdr lst)))
                   (list (nreverse results) lst))
               ))
      (partition-inner n coll))))

(defun partition-by (pred? coll)
  (labels ((partition-inner (lst results)
             (if (funcall pred? (car lst))
                 (return-from partition-by (list (nreverse results) lst))
                 (if (endp lst)
                     (list results nil)
                     (partition-inner (cdr lst) (cons (car lst) results))))))
    (partition-inner coll nil)
    ;; results
    ))
