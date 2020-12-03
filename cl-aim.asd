(defsystem "cl-aim"
  :version "0.1.0"
  :author "Alex Nelson"
  :license "MIT License"
  :depends-on ()
  :components ((:module "src"
                :components
                ((:file "main"))))
  :description "Experiment with declarative theorem provers."
  :in-order-to ((test-op (test-op "cl-aim/tests"))))

(defsystem "cl-aim/tests"
  :author "Alex Nelson"
  :license "MIT License"
  :depends-on ("cl-aim"
               "rove")
  :components ((:module "tests"
                :components
                ((:file "main"))))
  :description "Test system for cl-aim"
  :perform (test-op (op c) (symbol-call :rove :run c)))
