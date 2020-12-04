(defpackage #:cl-aim.fol.term-tests
  (:use #:cl #:rove #:cl-aim.fol.term))
(in-package #:cl-aim.fol.term-tests)

(deftest vars-test
    (let ((x (var 'x)))
      (is (eq (car (vars x))
              x)))
    (let ((g (fn :g (list (var 'x) (var 'y))))
          (h (fn :h (list (var 'y) (var 'z)))))
      (is (equal (mapcar #'var-name (vars (fn :f (list g (var 'x) h))))
                 (mapcar #'var-name (list (var 'x) (var 'y) (var 'z)))))))
