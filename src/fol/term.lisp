(defpackage #:cl-aim.fol.term
  (:use :cl)
  (:export term var var-name fn fn-name fn-args))
(in-package #:cl-aim.fol.term)

(defclass term ()
  ())

(defclass var (term)
  ((name :accessor var-name
         :initarg :name)))

(defclass fn (term)
  ((name :accessor fn-name
         :initarg :name)
   (args :accessor fn-args
         :initarg :args
         :type (vector term))))
