(defpackage #:cl-aim.fol.proof
  (:use :cl)
  (:documentation "Proof steps necessary for first-order logic."))
(in-package #:cl-aim.fol.proof)

(unless (boundp 'label-definitions)
  (defconstant label-definitions (make-hash-table)
    "Labels are used for reference in simple-justifications."))

(defun label (label-key step-or-formula)
  (declare (type symbol label-key))
  (setf (gethash label-key label-definitions) step-or-formula))

(defstruct (proof (:predicate proof?))
  (steps nil :type list))

(defstruct (by (:predicate simple-justification?))
  (references nil :type list))

(deftype justification ()
  (or 'by 'proof))

(defun justification? (x)
  (typep x 'justification))

(defun by-tautology ()
  (make-by :references '(:tautology)))

(defstruct (thm (:predicate thm?))
  (name)
  (statement (error "Thm requires a claim to prove") :type cl-aim.fol.formula)
  (proof (by-tautology) :type justification))

(defstruct (assume (:predicate assume?))
  (formula (error "Assume requires an assumption") :type cl-aim.fol.formula))

(defstruct (consider (:predicate consider?))
  (var-list nil :type list)
  (condition cl-aim.fol.verum :type cl-aim.fol.formula)
  (justification (by-tautology) :type justification))

(defgeneric then (step))
(defmethod then ((step consider))
  (assert (simple-justification? (consider-justification step)))
  (push :- (consider-justification step)))

;; TODO: (take term) OR (take (= var term))
(defstruct (take (:predicate take?))
  (term (error "Take requires a term to take") :type cl-aim.fol.term))

;; (defmacro take (term)
;;   (vector :take term))

;; TODO: focus thesis to be (assumption implies goal)
(defstruct (suppose (:predicate suppose?))
  (assumption (error "Suppose requires a supposition") :type cl-aim.fol.formula)
  (proof (by-tautology) :type justification))

(defstruct (per-cases (:predicate per-cases?))
  (justification (by-tautology))
  (cases nil :type (cons suppose)))

(defmethod then ((step per-cases))
  (assert (simple-justification? (per-cases-justification step)))
  (push :- (per-cases-justification step)))

(defstruct (thus (:predicate thus?))
  (formula (error "Thus requires a formula to proclaim.") :type cl-aim.fol.formula)
  (justification (by-tautology) :type justification))

(defmethod then ((step thus))
  (assert (simple-justification? (thus-justification step)))
  (push :- (thus-justification step)))

;; Proof steps:
;; - given
;; - take
;; - 

;; (defmacro given (var such-that formula)
;;   (assert (eq :such-that such-that))
;;   (list
;;    (assume (cl-aim.fol.formula:exists var such-that formula))
;;    (then (consider var such-that formula))))

;; (defmacro hence (formula &keyword (by nil))
;;   (then (thus formula (by by))))

