(defpackage #:cl-aim.fol.axiom
  (:use #:cl #:cl-aim.utils #:cl-aim.fol.term #:cl-aim.fol.formula)
  (:import-from #:cl-aim.fol.thm thm thm? thm-statement)
  (:export defaxiom modus-ponens generalize))
(in-package #:cl-aim.fol.axiom)

(defun make-thm (fm)
  (declare (type formula fm))
  (make-instance 'thm :conclude fm))

(defmacro defaxiom% (name params &body formula-body)
  (let ((tmp-sym (package-name *package*)))
    `(progn
       (in-package #:cl-aim.fol.axiom)
       (export ',(intern (string name) 'cl-aim.fol.axiom) 'cl-aim.fol.axiom)
       (defun ,(intern (string name) 'cl-aim.fol.axiom) ,params
         ,@formula-body)
       (in-package ,tmp-sym))))

;; MUST produce a thm.
(defmacro defaxiom* (name params &body formula-body)
  `(defun ,(intern (string name) 'cl-aim.fol.axiom) ,params
     ,@formula-body))

(defmacro defaxiom (name params &body formula-body)
  `(when (export ',(intern (string name) 'cl-aim.fol.axiom) 'cl-aim.fol.axiom)
     (defaxiom* ,name ,params ,@formula-body)))

(defun modus-ponens (p-implies-q p)
  "Given `|- p => q' and `|- p', we can infer `|- q'."
  (declare (type thm p p-implies-q))
  (assert (implies? (thm-statement p-implies-q)))
  (if (equal? (implies-premise (thm-statement p-implies-q))
              (thm-statement p))
      (make-instance 'thm :conclude (implies-conclusion (thm-statement p-implies-q)))
      (error "modus-ponens misapplied ~A trying to apply ~A" p-implies-q p)))

(defun generalize (x p)
  "From `|- p', we can infer `|- (forall x, p)'."
  (declare (type (or var symbol) x)
           (type thm p))
  (make-instance 'thm :conclude (forall (var x) (thm-statement p))))
