(defpackage cl-aim/tests/main
  (:use :cl
        :cl-aim
        :rove))
(in-package :cl-aim/tests/main)

;; NOTE: To run this test file, execute `(asdf:test-system :cl-aim)' in your Lisp.

(deftest test-target-1
  (testing "should (= 1 1) to be true"
    (ok (= 1 1))))
