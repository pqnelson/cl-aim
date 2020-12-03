(defpackage #:cl-aim.fol.formula
  (:use #:cl)
  (:import-from #:cl-aim.fol.term))
(in-package #:cl-aim.fol.formula)

(defclass formula ()
  ())

(defclass implies (formula)
  ((premise :initarg :premise
            :initform (error "Implies must have a premise")
            :type formula)
   (conclusion :initarg conclusion
               :initform (error "Implies must have a conclusion")
               :type formula)))

(defclass l-or (formula)
  ((disjuncts :initarg :disjuncts
              :type (vector formula))))

(defclass l-and (formula)
  ((conjuncts :initarg :disjuncts
              :type (vector formula))))

(defclass negation (formula)
  ((argument :initarg :formula
             :type formula)))

(defclass iff (formula)
  ((premise :initarg :premise
            :initform (error "Implies must have a premise")
            :type formula)
   (conclusion :initarg conclusion
               :initform (error "Implies must have a conclusion")
               :type formula)))

(defclass logical-constant (formula)
  ((name :type symbol
         :initarg :name
         :reader constant-name)))

(unless (boundp 'verum)
  (defconstant verum (make-instance 'logical-constant :name 'verum)
    "Represents logical truth constant."))

(unless (boundp 'contradiction)
  (defconstant contradiction (make-instance 'logical-constant :name 'contradiction)
    "The 'false' constant."))

(defclass forall (formula)
  ((var :initarg :var
        :type cl-aim.fol.term:var)
   (body :initarg :body
         :type formula)))

(defclass exists (formula)
  ((var :initarg :var
        :type cl-aim.fol.term:var)
   (body :initarg :body
         :type formula)))
