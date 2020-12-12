(defpackage #:cl-aim.fol.term-tests
  (:use #:cl #:rove #:cl-aim.fol.term))
(in-package #:cl-aim.fol.term-tests)

(deftest vars-test
    (let ((x (var 'x)))
      (ok (eq (car (vars x))
              x)))
    (let ((g (fn :g (list (var 'x) (var 'y))))
          (h (fn :h (list (var 'y) (var 'z)))))
      (ok (equal (mapcar #'var-name (vars (fn :f (list g (var 'x) h))))
                 (mapcar #'var-name (list (var 'x) (var 'y) (var 'z)))))))

(deftest var-equal?
  (ok (equal? (var 'x)
              (var 'x))))

(deftest print-var-test
    (let ((fstr (make-array '0 :element-type 'base-char
                               :fill-pointer 0
                               :adjustable t)))
      (with-output-to-string (s fstr)
        (format s "~A" (var 'xyz)))
      (ok (string-equal "xyz" fstr))))

(deftest print-fn-test
    (let ((fstr (make-array '0 :element-type 'base-char
                               :fill-pointer 0
                               :adjustable t)))
      (with-output-to-string (s fstr)
        (format s "~A" (fn 'f (list (var 'xyz)
                                    (fn 'g (list (var 'alpha)))
                                    (var 'beta)))))
      (ok (string-equal "#fn(f (xyz #fn(g (alpha)) beta))" fstr))))

(deftest fn-name-tests
    (ok (eq (fn-name (fn 'f (list (var 'x))))
            'f)))

(deftest fn-arity-tests
    (ok (= (arity (fn 'f (list (var 'a) (var 'b) (var 'c))))
           3))
    (ok (= (arity (fn 'f (list (var 'a))))
           1))
    (ok (= (arity (fn 'f nil))
           0)))

(deftest fn-equal?-tests
    (ok (equal? (fn 'f (list (var 'x)))
                (fn 'f (list (var 'x)))))
  (testing "Nested function equality"
    (ok (equal? (fn 'f (list (var 'x) (fn 'g (list (var 'y))) (var 'x)))
                (fn 'f (list (var 'x) (fn 'g (list (var 'y))) (var 'x))))))
  (testing "Different arguments do not match"
    (ng (equal? (fn 'f (list (var 'x)))
                (fn 'f (list (var 'y))))))
  (testing "Different function names should not match"
    (ng (equal? (fn 'g (list (var 'x)))
                (fn 'f (list (var 'y))))))
  ;; fail?
  (testing "Different arities should not match"
    (ng (equal? (fn 'g (list (var 'x)))
                (fn 'g (list (var 'x) (var 'y)))))))
