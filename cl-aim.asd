(defsystem "cl-aim"
  :version "0.1.0"
  :author "Alex Nelson"
  :license "MIT License"
  :depends-on ()
  :serial t
  :components ((:module "src"
                :components
                ((:file "utils")
                 (:file "main")
                 (:module "fol"
                  :components ((:file "term")
                               (:file "formula")
                               (:file "thm")
                               (:file "axiom")
                               (:file "hilbert")
                               (:file "lcf")
                               )))))
  :description "Experiment with declarative theorem provers."
  :in-order-to ((test-op (test-op "cl-aim/tests"))))

(defsystem "cl-aim/tests"
  :author "Alex Nelson"
  :license "MIT License"
  :depends-on ("cl-aim"
               "rove")
  :components ((:module "tests"
                :components
                ((:file "main")
                 (:module "fol"
                  :components
                  ((:file "term-tests")
                   (:file "formula-tests")
                   (:file "lcf-tests"))))))
  :description "Test system for cl-aim"
  :perform (test-op (op c) (symbol-call :rove :run c)))
