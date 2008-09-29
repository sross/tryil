;;; Copyright (c) 2006-2007, Sean Ross.  All rights reserved.
;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions
;;; are met:
;;;   * Redistributions of source code must retain the above copyright
;;;     notice, this list of conditions and the following disclaimer.
;;;   * Redistributions in binary form must reproduce the above
;;;     copyright notice, this list of conditions and the following
;;;     disclaimer in the documentation and/or other materials
;;;     provided with the distribution.
;;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
;;; OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
;;; WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
;;; DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
;;; GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
;;; WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;;; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;;; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#|

This is tryil a test framework for Common Lisp which was forked from Christopher Riesbeck's
excellent lisp-unit package.


Each assert should either print a #\. for a successful assert a #\F for a failed assert.
If the test fails an #\E should be printed.

running a test should return 2 values list of failed assertions and a list of passed assertions.

running a test-suite (or a list of test names) should collect all the returned assertions into 2 lists

if running a test fails the test suite should print an #\E (and throw the error, based on the value of *use-debugger*)
 and collect the names of the error'ed tests

the test suite should return 3 values a list of the passed assertions, as list of the failed assertions and a list of error'ed tests

a report function should also exist to report on the result of running a test suite

all printing should happen on *trace-output*)



a test suite should return

(a list of test-results containing
     -> test
     -> passed assertions
     -> failed assertions
     -> errors)

this will allow the most informative reporting on the results of tests.


|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Packages
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(cl:in-package :cl)

(defpackage #:tryil
  (:use #:common-lisp)
  (:export #:define-test #:run-all-tests #:run-tests #:assert=
           #:assert-eq #:assert-eql #:assert-equal #:assert-equalp
           #:assert-error #:assert-expands #:assert-false
           #:assert-equality #:assert-prints #:assert-true
           #:get-test-code #:get-tests
           #:remove-all-tests #:remove-tests
           #:logically-equal #:set-equal
           #:use-debugger
           #:with-test-listener
           #:*print-in-tests))

(in-package #:tryil)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Globals
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defparameter *test-output* *trace-output*)
(defparameter *print-in-tests* nil "When bound to true assert-prints will also print to standard-output")
(defparameter *test-listener* nil)
(defparameter *tests* (make-hash-table))
(defvar *passed-assertions* nil)
(defvar *failed-assertions* nil)
(defvar *test-name* nil "Bound to the name of the currently running test.")

;; printing of chars for each assertion
(defvar *report-on-progress* t
  "If true the *pass-char*, *fail-char* and *error-char* will be printed assertions are run.")
(defvar *pass-char* #\.)
(defvar *fail-char* #\F)
(defvar *error-char* #\E)


;;; If nil, errors in tests are caught and counted.
;;; If :ask, user is given option of entering debugger or not.
;;; If true and not :ask, debugger is entered.
(defparameter *use-debugger* nil)


;;;;;;;;;;;;;;;;;;
;;; Classes
;;;;;;;;;;;;;;;;;;

(defclass test ()
  ((name :accessor name-of :initarg :name)
   (code :accessor code-of :initarg :code)))

(defmethod print-object ((test test) stream)
  (print-unreadable-object (test stream :identity t :type t)
    (princ (name-of test) stream)))


(defclass test-result ()
  ((test :accessor test-for :initarg :test)
   (failed :accessor failed-assertions :initarg :failed)
   (passed :accessor passed-assertions :initarg :passed)
   (error :accessor error-of :initarg :error)))

(defmethod print-object ((result test-result) stream)
  (print-unreadable-object (result stream :type t)
    (format stream "For ~A: ~D Passed;  ~D Failed~@[;  An error occured running this test~]"
            (name-of (test-for result))
            (length (passed-assertions result))
            (length (failed-assertions result))
            (error-of result))))

(defun test-result (test failed passed error)
  (make-instance 'test-result :test test :failed failed :passed passed :error error))


(defmethod passedp ((result test-result))
  (and (not (failedp result)) (null (error-of result))))

(defmethod failedp ((result test-result))
  (not (null (failed-assertions result))))


(defclass assertion ()
  ((name :initarg :name :accessor name-of)
   (type :initarg :type :accessor type-for)
   (form :accessor form-of :initarg :form)
   (test :accessor test-of :initarg :test)
   (expected :accessor expected-of :initarg :expected)
   (actual :accessor actual-of :initarg :actual)
   (extras :accessor extras-of :initarg :extras)))

(defun get-failure-message (type)
  (case type
    (:error "~& ~@[Should have signalled ~{~S~^; ~} but saw~] ~{~S~^; ~}")
    (:macro "~& Should have expanded to ~{~S~^; ~} ~<~%~:;but saw ~{~S~^; ~}~>")
    (:output "~& Should have printed ~{~S~^; ~} ~<~%~:;but saw ~{~S~^; ~}~>")
    (t "~& Expected ~{~S~^; ~} ~<~%~:;but saw ~{~S~^; ~}~>")
    ))

(defun show-failure (type msg name form expected actual extras)
  (format t "~&~@[~S: ~]~S failed: " name form)
  (format t msg expected actual)
  (format t "~{~&   ~S => ~S~}~%" extras)
  type)

(defmethod print-object ((assertion assertion) stream)
  (if *print-escape*
      (call-next-method)
      (with-slots (name type form expected actual extras) assertion
        (show-failure type (get-failure-message type) name form expected actual extras))))


(defclass test-package-result ()
  ((test-results :accessor test-results-of :initform () :initarg :test-results)))

(defmethod total-tests ((obj test-package-result))
  (length (test-results-of obj)))

(defmethod total-passed-tests ((obj test-package-result))
  (count-if 'passedp (test-results-of obj)))

(defmethod total-failed-tests ((obj test-package-result))
  (count-if 'failedp (test-results-of obj)))

(defmethod total-passed-assertions ((obj test-package-result))
  (reduce '+ (test-results-of obj) :key (lambda (x) (length (passed-assertions x)))))

(defmethod total-failed-assertions ((obj test-package-result))
  (reduce '+ (test-results-of obj) :key (lambda (x) (length (failed-assertions x)))))

(defmethod total-assertions ((obj test-package-result))
  (+ (total-passed-assertions obj) (total-failed-assertions obj)))

(defmethod total-errors ((obj test-package-result))
  (count-if #'identity (test-results-of obj) :key 'error-of))

(defmethod print-object ((packaged test-package-result) stream)
  (if *print-escape* 
      (call-next-method)
      (print-readably packaged stream)))

      
(defun print-readably (result stream)
  (format stream "~&~%SUMMARY~6@TTotal~6@TPassed~7@TFailed~6@TErrors~%~@{~13A~13A~13A~13A~13A~%~}~%"
          "Tests"  (total-tests result) (total-passed-tests result) (total-failed-tests result) (total-errors result)
          "Assertions"  (total-assertions result) (total-passed-assertions result) (total-failed-assertions result) #\-)
  
  (unless (zerop (total-errors result))
    (format stream "~&~%;; Errors~%")
    (dolist (test-result (test-results-of result))
      (when (error-of test-result)
        (format stream "In test ~S caught  '~A'~%" (name-of (test-for test-result)) (error-of test-result)))))

  (unless (zerop (total-failed-assertions result))
    (format stream "~&~%;; Failed Assertions~%")
    (dolist (test-result (test-results-of result))
      (when (failed-assertions test-result)
        (mapc 'princ (failed-assertions test-result))))))


(defun wrap-in-result (results)
  (make-instance 'test-package-result :test-results results))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Macros
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; DEFINE-TEST
(defmacro define-test (name &body body)
  `(store-test-code ',name ',body))


;;; ASSERT macros
(defmacro assert-eq (expected form &rest extras)
 (expand-assert :equal form form expected extras :test #'eq))

(defmacro assert-eql (expected form &rest extras)
 (expand-assert :equal form form expected extras :test #'eql))

(defmacro assert-equal (expected form &rest extras)
 (expand-assert :equal form form expected extras :test #'equal))

(defmacro assert-equalp (expected form &rest extras)
 (expand-assert :equal form form expected extras :test #'equalp))

(defmacro assert= (expected form &rest extras)
 (expand-assert :equal form form expected extras :test #'=))

(defmacro assert-error (condition form &rest extras)
 (expand-assert :error form (expand-error-form form)
                condition extras))

(defmacro assert-expands (&environment env expansion form &rest extras)
  (expand-assert :macro form 
                 (expand-macro-form form env)
                 expansion extras))

(defmacro assert-false (form &rest extras)
  (expand-assert :result form form nil extras))
 
(defmacro assert-equality (test expected form &rest extras)
 (expand-assert :equal form form expected extras :test test))

(defmacro assert-prints (output form &rest extras)
  (expand-assert :output form (expand-output-form form)
                 output extras))

(defmacro assert-true (form &rest extras)
  (expand-assert :result form form t extras))


(defun expand-assert (type form body expected extras &key (test #'eql))
  `(internal-assert
    ,type ',form #'(lambda () ,body) #'(lambda () ,expected) ,(expand-extras extras), test))
  
(defun expand-error-form (form)
  `(handler-case ,form
     (condition (error) error)))


(defun expand-output-form (form)
  (let ((out (gensym)))
    `(let* ((,out (make-string-output-stream))
            (*standard-output* (if *print-in-tests* (make-broadcast-stream *standard-output* ,out) ,out)))
       ,form
       (get-output-stream-string ,out))))

(defun expand-macro-form (form env)
  `(macroexpand-1 ',form ,env))

(defun expand-extras (extras)
  `#'(lambda ()
       (list ,@(mapcan #'(lambda (form) (list `',form form)) extras))))
    

;;; RUN-TESTS

(defmacro run-tests (&rest names)
  `(run-tests-in *package* ,@names))

(defmacro run-tests-in (package &rest names)
  `(run-tests-fn (find-package ,package) ',names))

(defgeneric coerce-to-test (thing)
  (:method ((name symbol)) (get-test name))
  (:method ((test test)) test)
  (:method ((obj t)) (error "Cannot convert ~S to a test." obj)))

(defun run-tests-fn (package tests)
  (let ((*package* package)
        (tests-to-run (if (null tests)
                          (get-tests-in *package*)
                          (mapcar 'coerce-to-test tests))))
    (wrap-in-result (run-each-test tests-to-run))))
        

(defun use-debugger () *use-debugger*)
(defun (setf use-debugger) (newval) (setf *use-debugger* newval))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Public functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun get-test (name &optional (package *package*))
  (let ((table (get-package-table package)))
    (unless (null table)
      (gethash name table))))

(defun get-tests-in (&optional (package *package*))
  (let ((l nil)
        (table (get-package-table package)))
    (cond ((null table) nil)
          (t
           (maphash #'(lambda (key val)
                        (declare (ignore key))
                        (push val l))
                    table)
           l))))

(defun remove-tests (names &optional (package *package*))
  (let ((table (get-package-table package)))
    (unless (null table)
      (if (null names)
          (clrhash table)
          (dolist (name names)
            (remhash name table))))))

(defun remove-all-tests (&optional (package *package*))
  (if (null package)
      (clrhash *tests*)
      (remhash (find-package package) *tests*)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Private functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; DEFINE-TEST support
(defun get-package-table (package &key create)
  (let ((table (gethash (find-package package) *tests*)))
    (or table
        (when create
          (setf (gethash package *tests*)
                (make-hash-table))))))

(defun get-test-name (form)
  (if (atom form) form (cadr form)))

(defun store-test-code (name code &optional (package *package*))
  (setf (gethash name
                 (get-package-table package :create t))
        (make-instance 'test :name name :code code) ))


;;; ASSERTION support

(defun internal-assert (type form code-thunk expected-thunk extras test)
  (let* ((expected (multiple-value-list (funcall expected-thunk)))
         (actual (multiple-value-list (funcall code-thunk)))
         (passed (test-passed-p type expected actual test)))
    (record-result passed type form expected actual extras)
    passed))

(defun record-result (passed type form expected actual extras)
  (funcall (or *test-listener* 'default-listener)
           passed type *test-name* form expected actual 
           (and extras (funcall extras))))

(defun default-listener (passed type name form expected actual extras)
  (when *report-on-progress* (princ (if passed #\. #\F)))
  (let ((assertion (make-instance 'assertion :type type :form form :name name
                                  :expected expected :actual actual :extras extras)))
    (if passed
        (push assertion *passed-assertions*)
        (push assertion *failed-assertions*))))
              
         

(defun test-passed-p (type expected actual test)
  (ecase type
    (:error
     (or (eql (car actual) (car expected))
         (typep (car actual) (car expected))))
    (:equal
     (and (<= (length expected) (length actual))
          (every test expected actual)))
    (:macro
     (equal (car actual) (car expected)))
    (:output
     (string= (string-trim '(#\newline #\return #\space) 
                           (car actual))
              (car expected)))
    (:result
     (logically-equal (car actual) (car expected)))))


;;; RUN-TESTS support
(defun run-each-test (tests)
  (loop for test in tests
        collect (run-test test)))

(defun create-function (test)
  (coerce `(lambda nil ,@(code-of test)) 'function))

(defun run-test (test)
  (check-type test test)
  (let ((thunk (create-function test))
        (*passed-assertions* ())
        (*failed-assertions* ())
        (*test-name* (name-of test))
        (error nil))
    (block nil
      (handler-bind ((error #'(lambda (e)
                                (let ((*print-escape* nil))
                                  (princ #\E)
                                  (unless (use-debugger-p e)
                                    (return (setf error e)))))))
      (funcall thunk)))
    (test-result test *failed-assertions* *passed-assertions* error)))

(defun use-debugger-p (e)
  (and *use-debugger*
       (or (not (eql *use-debugger* :ask))
           (y-or-n-p "~A -- debug?" e))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Useful equality predicates for tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; (LOGICALLY-EQUAL x y) => true or false
;;;   Return true if x and y both false or both true

(defun logically-equal (x y)
  (eql (not x) (not y)))

;;; (SET-EQUAL l1 l2 :test) => true or false
;;;   Return true if every element of l1 is an element of l2
;;;   and vice versa.

(defun set-equal (l1 l2 &key (test #'equal))
  (and (listp l1)
       (listp l2)
       (subsetp l1 l2 :test test)
       (subsetp l2 l1 :test test)))


(provide "lisp-unit")


;; And in the good old tradition of eating our own dogfood here are some tests for tryil.

;; ...................

#|
(define-test sqrt
  (assert= 5 (sqrt 25))
  (assert= 6 (sqrt 36)))

(define-test plus 
  (assert= 5 (+ 1 4))
  (assert= 4 (+ 1 3))
  (assert= 3 (+ 1 4)))

(define-test division
  (assert-error 'division-by-zero (/ 1 0))
  (assert= 0 (/ 1 0)))
  
  

(princ (run-tests))

|#