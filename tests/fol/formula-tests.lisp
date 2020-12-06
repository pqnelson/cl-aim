(defpackage #:cl-aim.fol.formula-tests
  (:import-from #:cl-aim.fol.term var fn)
  (:use #:cl #:rove #:cl-aim.fol.formula))
(in-package #:cl-aim.fol.formula-tests)

;; test all the print-objects
;; test the nnf
(labels ((prints-to? (obj expected-str)
           (let ((fstr (make-array '0 :element-type 'base-char
                                      :fill-pointer 0
                                      :adjustable t)))
             (with-output-to-string (s fstr)
               (format s "~A" obj))
             (string-equal expected-str fstr)))
         (q (x)
           (make-instance 'predicate :name :q
                                     :args (list (var x))))
         (p (x)
           (make-instance 'predicate :name :p
                                     :args (list (var x)))))
  (deftest print-iff-test
    (ok (prints-to? (iff (p 'x)
                         (q 'y))
                    "(iff #pred(P X) #pred(Q Y))")))
  (deftest print-implies-test
    (ok (prints-to? (implies (p 'x)
                             (q 'y))
                    "(implies #pred(P X) #pred(Q Y))")))
  (deftest print-land-test
    (ok (prints-to? (land (p 'x)
                          (q 'y))
                    "(land #pred(P X) #pred(Q Y))")))
  (deftest print-lor-test
    (ok (prints-to? (lor (p 'x)
                         (q 'y))
                    "(lor #pred(P X) #pred(Q Y))")))
  (deftest print-not-test
    (ok (prints-to? (make-instance 'negation :formula (p 'x))
                    "(#not #pred(P X))")))
  (deftest print-constant-test
    (ok (prints-to? verum
                    "#const(VERUM)"))
    (ok (prints-to? contradiction
                    "#const(CONTRADICTION)")))
  (deftest print-exists-test
    (ok (prints-to? (exists 'x (p 'x))
                    "(#exists X #pred(P X))"))
    (ok (prints-to? (exists 'y (q 'y))
                    "(#exists Y #pred(Q Y))"))
    )
  (deftest print-forall-test
    (ok (prints-to? (forall 'x (p 'x))
                    "(#forall X #pred(P X))"))
    (ok (prints-to? (forall 'y (q 'y))
                    "(#forall Y #pred(Q Y))"))
    ))

(deftest nnf-tests
  (labels ((p (x) (make-instance 'predicate
                                 :name 'P
                                 :args (list (var x))))
           (q (x) (make-instance 'predicate
                                 :name 'Q
                                 :args (list (var x)))))
    (ok (equal? (->nnf
                 (l-neg (make-instance 'exists
                                        :var (var 'x)
                                        :body (p 'x))))
                (forall 'x (l-neg (p 'x)))))
    (ok (equal? (->nnf
                 (l-neg (make-instance 'forall
                                        :var (var 'x)
                                        :body (p 'x))))
                (exists 'x (l-neg (p 'x)))))
    (ok (equal? (->nnf
                 (make-instance
                  'implies
                  :premise (make-instance 'forall
                                          :var (var 'x)
                                          :body (p 'x))
                  :conclusion (make-instance 'forall
                                             :var (var 'y)
                                             :body (q 'y))))
                (lor (exists 'x (l-neg (p 'x)))
                     (forall 'y (q 'y)))))
    (ok (equal? (->nnf
                 (implies
                  (forall 'x (p 'x))
                  (iff (exists 'y (q 'y))
                       (exists 'z (land (p 'z) (q 'z))))))
                (lor (exists 'x (l-neg (p 'x)))
                     (land (forall 'y (l-neg (q 'y)))
                           (forall 'z (lor (l-neg (p 'z))
                                           (l-neg (q 'z)))))
                     (land (exists 'y (q 'y))
                           (exists 'z (land (p 'z)
                                            (q 'z)))))))
    ))


(deftest pull-quantifiers-test
  (labels ((p (x)
             (make-instance 'predicate :name 'p
                                       :args (list (var x))))
           (q (x)
             (make-instance 'predicate :name 'q
                                       :args (list (var x))))
           (r (x)
             (make-instance 'predicate :name 'r
                                       :args (list (var x))))
           )
    (ok (equal? (pull-quantifiers (lor (forall 'x (p 'x))
                                       (q 'y)
                                       (exists 'x (r 'x))))
                (forall 'x (exists 'x (lor (p 'x)
                                           (q 'y)
                                           (r 'x))))))))

(deftest simplifies-test
  (labels ((make-prop (p) (make-instance 'predicate :name p :args nil)))
    (ok (equal? (simplify (implies
                           (implies verum (iff (make-prop 'x) contradiction))
                           (l-neg (lor (make-prop 'y)
                                        (land (make-prop 'z) contradiction)
                                        ))))
                (implies (l-neg (make-prop 'x))
                         (l-neg (make-prop 'y)))))))

(deftest skolemize-test
  (labels ((lt (a b)
             (make-instance 'predicate
                            :name :LT
                            :args (list a b)))
           (times (a b)
             (fn :* (list a b)))
           (f (x)
             (cl-aim.fol.formula::skolem-symbol
              (concatenate 'string "f_" (symbol-name x)))))
    (ok
     (equal?
      (skolemize
       (exists (var 'y)
               (implies (lt (var 'x) (var 'y))
                        (forall (var 'u)
                                (exists (var 'v)
                                        (lt (times (var 'x) (var 'u))
                                            (times (var 'y) (var 'v))))))))
      (lor (l-neg (lt (var 'x) (fn (f 'y) (list (var 'x)))))
           (lt (times (var 'x) (var 'u))
               (times (fn (f 'y) (list (var 'x)))
                      (fn (f 'v) (list (var 'x) (var 'u))))))))))
