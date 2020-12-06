(defpackage #:cl-aim.fol.thm
  (:import-from #:cl-aim.fol.formula formula implies?)
  (:use #:cl #:cl-aim.utils)
  (:export thm thm-statement thm? make-thm thm-implies equal?))
(in-package #:cl-aim.fol.thm)

(defclass thm ()
  ((conclusion :reader thm-statement
               :initarg :conclude
               :initform (error "Thm needs a statement to conclude.")
               :type formula)))

(defmethod print-object ((object thm) stream)
  (format stream "(|- ~A)" (thm-statement object)))

(defun make-thm (fm)
  (declare (type formula fm))
  (make-instance 'thm :conclude fm))

(defun thm? (x) (typep x 'thm))

(defun thm-implies? (th)
  ;; (declare (type thm th))
  (and (thm? th)
       (implies? (thm-statement th))))

(deftype thm-implies ()
  `(satisfies thm-implies?))

(defmethod equal? ((lhs thm) (rhs thm))
  (equal? (thm-statement lhs)
          (thm-statement rhs)))

(defmacro defthm (name params &body formula-body)
  `(progn
     (defun ,(intern (string name) 'cl-aim.fol.thm) ,params
       ,@formula-body)
     (export ',(intern (string name) 'cl-aim.fol.thm) 'cl-aim.fol.thm)
     ))
