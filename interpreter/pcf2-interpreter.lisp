;; Interpreter for the PCF2 bytecode

(defpackage :pcf2-interpreter 
  (:use :pcf2-bc :skew-list :common-lisp :utils :unit)
  (:export run-opcodes
           init-state
           setup-labels
           pcf2-state
           add-to-watch-list
           add-to-watch-list-bit
           remove-from-watch-list
           set-debug-ptrs
           unset-debug-ptrs))
(in-package :pcf2-interpreter)

(defparameter *debug-output* nil)
;;;(defparameter *error-output* nil)

(defstruct (pcf2-state
             (:print-function
              (lambda (struct stream depth)
                (declare (ignore depth))
                (format stream "PCF2 State: ~%")
                (format stream "Memory: (")
                ;(skew-map #'(lambda (x) (format stream "~A " x))
                ;          (pcf2-state-memory struct))
                (format stream ")~%")
                (format stream "Baseptr: ~A~%" (pcf2-state-baseptr struct))
                (format stream "Insptr: ~A~%" (pcf2-state-iptr struct))
                (format stream "Call stack: ~A~%" (pcf2-state-call-stack struct))
                (format stream "Labels: ~A~%" (pcf2-state-lbls struct))
                (format stream "Total gates emitted: ~A~%" (pcf2-state-gates-emitted struct))
                (format stream "Total non-xor gates emitted: ~A~%" (pcf2-state-non-xor-gates-emitted struct))
                )
              )
             )
  (memory)
  (baseptr 0 :type (integer 0))
  (iptr)
  (lbls)
  (call-stack)
  (alice-inputs)
  (bob-inputs)
  (gates-emitted 0 :type (integer 0))
  (non-xor-gates-emitted 0 :type (integer 0))
  (:documentation "The memory random access list is the wire table + pointers + constant values.  The baseptr is the pointer in the memory array to the beginning of the current stack frame.  The iptr is the pointer to the next opcode.  The lbls slot is the hash table of labels to the beginning of the list of opcodes they correspond to.

The functions that operate on pcf2-state objects should treat these objects as immutable.  Thus we use a random access list rather than an array, and a linked list to create stack frames.  In doing so we can support debugging much effectively and potentially even allow reversible debugging of PCF2 programs.")
  )

(defstruct (input-bit
             (:print-function
              (lambda (struct stream depth)
                (declare (ignore depth))
                (format stream "[~A]" (input-bit-val struct))
                )
              )
             )
  (val 0 :type bit)
  (:documentation "This type represents an \"unknown\" bit that is an input from a party.")
  )

(defun setup-test-state (op &optional (memsize 10))
  (with-input-from-string (in-stream "0
0")
    (init-state memsize (list op) in-stream 0 0)
    )
  )

(defun init-state (memsize opcodes inputs-file alice-input-size bob-input-size)
  "Initialize a PCF2 state object with \"memsize\" memory elements.  Alice and Bob inputs are read from the inputs-file parameter, which should be a stream"
  (declare (type stream inputs-file)
           (optimize (debug 3) (speed 0)))
  (let ((alice-input (parse-integer (read-line inputs-file) :radix 16))
        (bob-input (parse-integer (read-line inputs-file) :radix 16))
        )
    (let ((newstate (make-pcf2-state :memory
                                     ;(let ((m nil))
                                     ;  (loop for i from 2 to memsize do
                                     ;       (setf m (skew-cons 0 m))
                                     ;       )
                                     ;  (setf m (skew-cons 1 m))
                                     ;  m)
                                     (let ((m (make-array memsize :initial-element 0))
                                           )
                                       (setf (aref m 0) 1)
                                       m
                                       )
                                     :baseptr 1
                                     :iptr opcodes
                                     :lbls (make-hash-table :test 'equalp)
                                     :call-stack nil
                                     :alice-inputs (skew-reverse
                                                    (cdr (reduce (lambda (st x)
                                                                   (declare (ignore x))
                                                                   (let ((val (car st))
                                                                         (lst (cdr st))
                                                                         )
                                                                     (cons (ash val -1) (skew-cons 
                                                                                         (make-input-bit
                                                                                          :val (mod val 2))
                                                                                         lst))
                                                                     )
                                                                   )
                                                                 (loop for i from 1 to alice-input-size collect i)
                                                                 :initial-value (cons alice-input nil))))
                                     :bob-inputs (skew-reverse
                                                  (cdr (reduce (lambda (st x)
                                                                 (declare (ignore x))
                                                                 (let ((val (car st))
                                                                       (lst (cdr st))
                                                                       )
                                                                   (cons (ash val -1) (skew-cons 
                                                                                       (make-input-bit
                                                                                        :val (mod val 2))
                                                                                       lst))
                                                                   )
                                                                 )
                                                               (loop for i from 1 to bob-input-size collect i)
                                                               :initial-value (cons bob-input nil))))
                                     )
            )
          )
      newstate
      )
    )
  )

(defun get-party-input (state idx party)
  (declare (optimize (debug 0) (speed 3)))
  (cond
    ((equalp party "alice") (skew-ref idx (pcf2-state-alice-inputs state)))
    ((equalp party "bob") (skew-ref idx (pcf2-state-bob-inputs state)))
    (t (error 'unknown-party))
    )
  )

(defmacro add-label (str opcodes state)
  `(progn
     (setf (gethash ,str (pcf2-state-lbls ,state)) ,opcodes)
     state
     )
  )

(defun setup-labels (opcodes state)
  (if opcodes
      (typecase (first opcodes)
        (pcf2-bc:label (with-slots (str) (first opcodes)
                         (let ((state (add-label str opcodes state)))
                           (setup-labels (rest opcodes) state)
                           )
                         )
                       )
        (t 
         (setup-labels (rest opcodes) state))
        )
      state
      )
  )

(defmacro get-state-val (state idx)
  ;`(skew-ref ,idx (pcf2-state-memory ,state))
  `(aref (pcf2-state-memory ,state) ,idx)
  )

(defparameter *x* 0)

(defparameter *watch-list* (make-hash-table))

(defparameter *ptrs* (make-hash-table))
(defparameter *debug-ptrs* nil)

(defun set-debug-ptrs () (setf *debug-ptrs* t))
(defun unset-debug-ptrs () (setf *debug-ptrs* nil))

(defun add-to-watch-list-bit (idx)
  (setf (gethash idx *watch-list*) 'bool)
  )

(defun add-to-watch-list (idx)
  (setf (gethash idx *watch-list*) t)
  )

(defun remove-from-watch-list (idx)
  (setf (gethash idx *watch-list*) nil)
  )

(defmacro set-state-val (state idx val)
  "Sets the value at index \"idx\" of \"state\" to \"val\".  This macro also emits debugging code."
  (let ((idxsym (gensym))
        )
    `(let ((st ,state)
           (val ,val)
           (,idxsym ,idx)
           )
       (aif (gethash ,idxsym *watch-list*)
            (if (equal it 'bool)
                (if (not (typep val '(or input-bit bit)))
                    (error (with-output-to-string (str)
                             (format str "Value at position ~D is ~A, which is not a bit!"
                                     ,idxsym
                                     val)
                             str)))
                (if *debug-output*
                    (format *error-output* "~&Setting state value ~D to ~A~%" ,idx ,val))))
       (let ((newstate (make-pcf2-state :baseptr (pcf2-state-baseptr st)
                                        :iptr (pcf2-state-iptr st)
                                        :lbls (pcf2-state-lbls st)
                                        :call-stack (pcf2-state-call-stack st)
                                        :memory ;(skew-update ,idx ,val (pcf2-state-memory st))
                                        (progn
                                          (setf (aref (pcf2-state-memory st) ,idxsym) ,val)
                                          (pcf2-state-memory st)
                                          )
                                        :alice-inputs (pcf2-state-alice-inputs ,state)
                                        :bob-inputs (pcf2-state-bob-inputs ,state)
                                        :gates-emitted (pcf2-state-gates-emitted ,state)
                                        :non-xor-gates-emitted (pcf2-state-non-xor-gates-emitted ,state)
                                        )
               )
             )
         newstate)
       )
    )
  )
  
(defmacro find-label (state label)
  (let ((sym (gensym))
        )
    `(let ((,sym (gethash ,label (pcf2-state-lbls ,state)))
           )
       (assert ,sym)
       ,sym
       )
    )
  )

(defmacro update-state (state memory baseptr iptr call-stack)
  `(let ((st ,state))
     (let ((newstate (make-pcf2-state :baseptr (pcf2-state-baseptr st)
                                      :iptr (pcf2-state-iptr st)
                                      :lbls (pcf2-state-lbls st)
                                      :call-stack (pcf2-state-call-stack st)
                                      :memory (pcf2-state-memory st)
                                      :alice-inputs (pcf2-state-alice-inputs st)
                                      :bob-inputs (pcf2-state-bob-inputs st)
                                      :gates-emitted (pcf2-state-gates-emitted st)
                                      :non-xor-gates-emitted (pcf2-state-non-xor-gates-emitted st)
                                      )
             )
           )
       ,(if memory
            `(setf (pcf2-state-memory newstate) ,memory)
            )
       ,(if baseptr
            `(progn
               (if *debug-output*
                   (format *error-output* "~%Setting base pointer: ~A~%" ,baseptr)
                   )
               (setf (pcf2-state-baseptr newstate) ,baseptr)
               )
            )
       ,(if iptr
            `(setf (pcf2-state-iptr newstate) ,iptr)
            )
       ,(if call-stack
            `(setf (pcf2-state-call-stack newstate) ,call-stack)
            )
       newstate)
     )
  )

(defmacro incf-non-xor (state)
  `(let ((st ,state))
     (let ((newstate (make-pcf2-state :baseptr (pcf2-state-baseptr st)
                                      :iptr (pcf2-state-iptr st)
                                      :lbls (pcf2-state-lbls st)
                                      :call-stack (pcf2-state-call-stack st)
                                      :memory (pcf2-state-memory st)
                                      :alice-inputs (pcf2-state-alice-inputs st)
                                      :bob-inputs (pcf2-state-bob-inputs st)
                                      :gates-emitted (pcf2-state-gates-emitted st)
                                      :non-xor-gates-emitted (pcf2-state-non-xor-gates-emitted st)
                                      )
             )
           )
       (incf (pcf2-state-gates-emitted newstate))
       (incf (pcf2-state-non-xor-gates-emitted newstate))
       newstate)
     )
  )

(defmacro incf-xor (state)
  `(let ((st ,state))
     (let ((newstate (make-pcf2-state :baseptr (pcf2-state-baseptr st)
                                      :iptr (pcf2-state-iptr st)
                                      :lbls (pcf2-state-lbls st)
                                      :call-stack (pcf2-state-call-stack st)
                                      :memory (pcf2-state-memory st)
                                      :alice-inputs (pcf2-state-alice-inputs st)
                                      :bob-inputs (pcf2-state-bob-inputs st)
                                      :gates-emitted (pcf2-state-gates-emitted st)
                                      :non-xor-gates-emitted (pcf2-state-non-xor-gates-emitted st)
                                      )
             )
           )
       (incf (pcf2-state-gates-emitted newstate))
       newstate)
     )
  )

(defun run-opcodes (state)
  (declare (type pcf2-state state)
           (optimize (speed 3) (debug 0))
           )
  (labels ((run-opcodes* (state)
             (let ((opcodes (pcf2-state-iptr state))
                   )
               (if (null opcodes)
                   state;(loop for i from 65 to (+ 65 31) collect (aref (pcf2-state-memory state) i))
                   (let* ((op (first opcodes))
                          (newstate (run-opcode state op))
                          (state (update-state newstate
                                               nil 
                                               nil 
                                               (rest (pcf2-state-iptr newstate)) 
                                               nil))
                          )
                     (run-opcodes* state)
                     )
                   )
               )
             )
           )
    (let ((state (update-state state nil nil (cons (first (pcf2-state-iptr state)) 
                                                   (gethash "pcfentry" (pcf2-state-lbls state) 
                                                            (gethash "PCFENTRY" (pcf2-state-lbls state) 'fail))) 
                               nil))
          )
      (setf *ptrs* (make-hash-table))
      (run-opcodes* state)
      )
    )
  )


(defgeneric run-opcode (state opcode)
  (:documentation "Each PCF2 opcode will take in a program state and update it in some way")
  )

(defmethod-ut run-opcode ((state pcf2-state) (opcode initbase))
  (with-slots (base) opcode
    (if *debug-output*
        (format *error-output* "~&Setting initial base pointer: ~D~%" base)
        )
    (update-state (update-state state nil (+ (pcf2-state-baseptr state) base) nil nil)
                  nil nil (gethash "main" (pcf2-state-lbls state) 
                                   (gethash "MAIN" (pcf2-state-lbls state) 'fail)) nil)
    )
  :tests
  ((initbase-works . (lambda ()
                       (and
                        (with-input-from-string (in-stream "0
0")
                          (let* ((op (make-instance 'initbase :base 6))
                                 (state (init-state 10 op in-stream 0 0))
                                 )
                            (setf state (run-opcode state op))
                            ;; Baseptr will be initialized to 1, so the result of the op is 7
                            (= (pcf2-state-baseptr state) 7)
                            )
                          )
                        (with-input-from-string (in-stream "0
0")
                          (let* ((op (make-instance 'initbase :base #x7FFFFFFE))
                                 (state (init-state 10 op in-stream 0 0))
                                 )
                            (setf state (run-opcode state op))
                            (= (pcf2-state-baseptr state) #x7FFFFFFF)
                            )
                          )
                         )
                       )
                   )
   (initbase-main . (lambda ()
                      (with-input-from-string (in-stream "0
0")
                        (let* ((op (make-instance 'initbase :base 6))
                               (state (init-state 10 (list op) in-stream 0 0))
                               )
                          (setf state (add-label "main" (list op) state))
                          (setf state (run-opcode state op))
                          ;; Baseptr will be initialized to 1, so the result of the op is 7
                          (equalp (pcf2-state-iptr state) (list op))
                          )
                        )
                      )
                  )
   )
  )

(defmacro check-mux-cnd ()
  ;; '(assert (not (zerop (let ((s-val (get-state-val state 0))
  ;;                           )
  ;;                       (etypecase s-val
  ;;                         (bit s-val)
  ;;                         (input-bit (input-bit-val s-val))
  ;;                         )
  ;;                       )
  ;;                     )))
  )

(defmethod run-opcode ((state pcf2-state) (opcode call))
  (declare (optimize (debug 3) (speed 0) (safety 3)))
  (with-slots (newbase fname) opcode
    (let ((newbase (+ newbase (pcf2-state-baseptr state)))
          )
      (check-mux-cnd)
      (if *debug-output*
          (format *error-output* "~&Function ~A, new base: ~A~%" fname newbase))
      (cond
        ((or (string-equal fname "alice")
             (string-equal fname "bob"))
                                        ;(update-state state nil nil nil nil)
         (let ((input-pos (reduce (lambda (val b)
                                    (declare (type bit b))
                                    (+ (ash val 1) b)
                                    )
                                  (loop for i from 1 to 32 collect
                                       (the bit (get-state-val state (- newbase i)))
                                       )
                                  )
                 )
               )
           (if *debug-output*
               (format *error-output* "~&Getting input ~A for ~A~%" input-pos fname))
           (let ((state (reduce
                         #'(lambda (st x)
                             (set-state-val st (+ newbase x) (get-party-input state (+ input-pos x) fname))
                             )
                         (loop for i from 0 to 31 collect i)
                         :initial-value state)
                   )
                 )
             (if *debug-output*
                 (format *error-output* "~&Input ~A for ~A: ~A~%" input-pos fname (loop for i from 0 to 31 collect (get-state-val state (+ newbase i)))))
             state
             )
           )
         )
        ((string-equal fname "output_alice")
         (format t "~&Output for Alice: ~A~%" (loop for i from 32 downto 1 collect (get-state-val state (- newbase i))))
         state
         )
        ((string-equal fname "output_bob")
         (format t "~&Output for Bob: ~A~%" (loop for i from 32 downto 1 collect (get-state-val state (- newbase i))))
         state
         )
        (t 
         (let ((new-iptr (find-label state fname))
               (call-stack (cons (cons (pcf2-state-iptr state)
                                       (pcf2-state-baseptr state))
                                 (pcf2-state-call-stack state)))
               )
           ;(format t "~&Calling function ~A new base ptr: ~A~%" fname newbase)
           ;(format t "~&Call stack: ~A~%" (mapcar #'cdr call-stack))
           (update-state state nil newbase new-iptr call-stack)
           )
         )
        )
      )
    )
  )

(defmethod run-opcode ((st pcf2-state) (opcode clear))
  (with-slots (localsize) opcode
    (let ((state st))
      (if *debug-output*
          (format *error-output* "~&Clearing region: ~D - ~D~%" 
                  (pcf2-state-baseptr state)
                  (+ (pcf2-state-baseptr state) localsize))
          )
      (loop for i from (pcf2-state-baseptr state) to 
         (+ (pcf2-state-baseptr state) localsize) do
           (set-state-val state i 0)
           )
      state
      )
    )
  )

(defmethod run-opcode ((st pcf2-state) (opcode ret))
  (with-slots (value) opcode
    (let ((state st)
          )
      (if (pcf2-state-call-stack state)
          (let ((iptrbaseptr (first (pcf2-state-call-stack state)))
                (call-stack (rest (pcf2-state-call-stack state)))
                )
            (format *error-output* "~&Returning from funcall.  Clearing region from ~D to ~D~%"
                    (pcf2-state-baseptr state)
                    value)
            (check-mux-cnd)
            (loop for i from (pcf2-state-baseptr state) to 
               (+ (pcf2-state-baseptr state) value) do
                 (setf state (set-state-val state i 0))
                 )
            (update-state state nil (cdr iptrbaseptr) (car iptrbaseptr) call-stack) 
            )
          state
          )
      )
    )
  )

 (defmethod run-opcode ((state pcf2-state) (opcode branch))
   (with-slots (cnd targ) opcode
 ;    (if (string-equal targ "$27") (assert nil))
     (let ((cnd-v (get-state-val state (+ (pcf2-state-baseptr state) cnd)))
           (targ (find-label state targ))
           )
       (declare (type bit cnd-v))
       (if *debug-output*
           (format *error-output* "~&Branch: ~A~%" opcode)
           )
       (if (zerop cnd-v)
           state
           (update-state state nil nil targ nil)
           )
       )
     )
   )

 (defmethod run-opcode ((state pcf2-state) (opcode add))
   (with-slots (dest op1 op2) opcode
     (let* ((true-op1 (+ op1 (pcf2-state-baseptr state)))
            (true-op2 (+ op2 (pcf2-state-baseptr state)))
            (true-dest (+ dest (pcf2-state-baseptr state)))
            (x (get-state-val state true-op1))
            (y (get-state-val state true-op2))
            )
       (declare (type integer x y))
       (if *debug-output*
           (format *error-output* "~&Add(~A,~A,~A): ~A + ~A = ~A~%" op1 op2 dest x y (+ x y))
           )
       (set-state-val state true-dest (+ x y))
       )
     )
   )

(defmethod run-opcode ((state pcf2-state) (opcode join))
  (with-slots (dest op1) opcode
    (let ((true-op1 (mapcar (lambda (x) (get-state-val state (+ x (pcf2-state-baseptr state)))) op1))
          (true-dest (+ dest (pcf2-state-baseptr state)))
          )
      (if *debug-output*
          (format *error-output* "~&Join: ~A" true-op1)
          )
      (set-state-val state true-dest
                     (reduce (lambda (v x)
                               (declare (type bit x))
                               (+ (ash v 1) x)
                               )
                             (reverse true-op1)
                             :initial-value 0
                             )
                     )
      )
    )
  )

 (defmethod run-opcode ((state pcf2-state) (opcode bits))
   (with-slots (dest op1) opcode
     (let* ((true-op1 (+ op1 (pcf2-state-baseptr state)))
            (true-dest (mapcar
                        (lambda (x) (+ x (pcf2-state-baseptr state)))
                        dest))
            (val (get-state-val state true-op1))
            )
       (car 
        (reduce (lambda (stv x)
                  (let ((state (car stv))
                        (val (cdr stv))
                        )
                    (cons 
                     (set-state-val state x (mod val 2))
                     (ash val -1)
                     )
                    )
                  )
                true-dest :initial-value (cons state val))
        )
       )
     )
   )

 (defmethod run-opcode ((state pcf2-state) (opcode sub))
   (with-slots (dest op1 op2) opcode
     (let* ((true-op1 (+ op1 (pcf2-state-baseptr state)))
            (true-op2 (+ op2 (pcf2-state-baseptr state)))
            (true-dest (+ dest (pcf2-state-baseptr state)))
            (x (get-state-val state true-op1))
            (y (get-state-val state true-op2))
            )
       (declare (type integer x y))
       (set-state-val state true-dest (- x y))
       )
     )
   )

 (defmethod run-opcode ((state pcf2-state) (opcode mul))
   (with-slots (dest op1 op2) opcode
     (let* ((true-op1 (+ op1 (pcf2-state-baseptr state)))
            (true-op2 (+ op2 (pcf2-state-baseptr state)))
            (true-dest (+ dest (pcf2-state-baseptr state)))
            (x (get-state-val state true-op1))
            (y (get-state-val state true-op2))
            )
       (declare (type integer x y))
       (if *debug-output*
           (format *error-output* "~&mul: ~A * ~A = ~A~&" x y (* x y))
           )
       (set-state-val state true-dest (* x y))
       )
     )
   )

(defmethod-ut run-opcode ((state pcf2-state) (opcode const))
  (with-slots (dest op1) opcode
    (let* ((true-dest (+ dest (pcf2-state-baseptr state)))
           )
      (if *debug-output*
          (format *error-output* "const: ~A to ~A~%" op1 true-dest)
          )
      (set-state-val state true-dest op1)
      )
    )
  :tests
  ((const-works . (lambda ()
                    (let* ((op (make-instance 'const :dest 0 :op1 #xF1))
                           (state (setup-test-state op))
                           )
                      (setf state (run-opcode state op))
                      (= (get-state-val state 1) #xF1)
                      )
                    )
                )
   (only-dest-change .
                     (lambda ()
                       (let* ((op (make-instance 'const :dest 0 :op1 #xF1))
                              (state (setup-test-state op))
                              )
                         (let ((res t)
                               (saved-state (copy-seq (pcf2-state-memory state)))
                               )
                           (setf state (run-opcode state op))
                           (loop for i from 0 to (1- (length (pcf2-state-memory state)))
                              unless (= 1 i)
                              do
                                (setf res (and res (= (aref (pcf2-state-memory state) i)
                                                      (aref saved-state i)
                                                      )
                                               )
                                      )
                                )
                           res
                           )
                         )
                       )
                     )
   )              
  )

(defmethod-ut run-opcode ((state pcf2-state) (opcode copy))
  (with-slots (dest op1 op2) opcode
    (let ((true-op1 (+ op1 (pcf2-state-baseptr state)))
          (true-dest (+ dest (pcf2-state-baseptr state)))
          )
      (reduce (lambda (state x)
                (set-state-val state (+ x true-dest)
                               (get-state-val state (+ x true-op1))
                               )
                )
              (loop for i from 0 to (1- op2) collect i)
              :initial-value state)
      )
    )
  :tests
  ((copy-32 . (lambda ()
                (let* ((op (make-instance 'copy :dest 32 :op1 0 :op2 32))
                       (state (setup-test-state op 128))
                       )
                  (loop for i from 0 to 31 do
                       (setf state (set-state-val state (1+ i) (mod i 2)))
                       )
                  (setf state (run-opcode state op))
                  (let ((res t))
                    (loop for i from 0 to 31 do
                         (setf res (and res
                                        (= (get-state-val state (+ 33 i))
                                           (get-state-val state (+  1 i))
                                           )
                                        )
                               )
                         )
                    res
                    )
                  )
                )
            )
   (copy-1 . (lambda ()
               (let* ((op (make-instance 'copy :dest 1 :op1 0 :op2 1))
                      (state (setup-test-state op))
                      )
                 (setf state (set-state-val state 1 #xFFEE))
                 (setf state (run-opcode state op))
                 (= (get-state-val state 2)
                    (get-state-val state 1)
                    #xFFEE)
                 )
               )
           )
   )
  )

(defmethod run-opcode ((state pcf2-state) (opcode copy-indir)
                       )
  (declare (optimize (debug 3) (speed 0)))
  (with-slots (dest op1 op2) opcode
    (let ((true-op1 (+ op1 (pcf2-state-baseptr state)))
          (true-dest (+ dest (pcf2-state-baseptr state)))
          )
      (if *debug-ptrs*
          (assert (gethash true-op1 *ptrs*))
          )
      (if *debug-output*
          (format *error-output* "~A -> ~A~%" 
                  (get-state-val state true-op1) 
                  (loop for i from 0 to (1- op2) collect (get-state-val state (+ i (get-state-val state true-op1)))))
          )
      (reduce (lambda (state i) 
                (set-state-val state (+ i true-dest)
                               (get-state-val state
                                              (+ i (get-state-val state
                                                                  true-op1))))
                )
              (loop for i from 0 to (1- op2) collect i) :initial-value state)
      )
    )
  )

(defmethod run-opcode ((state pcf2-state) (opcode indir-copy))
  (declare (optimize (debug 3) (speed 0)))
  (with-slots (dest op1 op2) opcode
    (let ((true-op1 (+ op1 (pcf2-state-baseptr state)))
          (true-dest (get-state-val state (+ dest (pcf2-state-baseptr state))))
          )
      (if *debug-ptrs*
          (assert (gethash (+ dest (pcf2-state-baseptr state)) *ptrs*))
          )
      (if *debug-output*
          (format *error-output* "~A <- ~A~%" true-dest (loop for i from 0 to (1- op2) collect (get-state-val state (+ true-op1 i))))
          )
      (reduce (lambda (st i) 
                (set-state-val st
                               (+ i true-dest)
                               (get-state-val st (+ i true-op1))
                               )
                ) (loop for i from 0 to (1- op2) collect i) :initial-value state)
      )
    )
  )

(defmethod run-opcode ((state pcf2-state) (opcode mkptr))
  (with-slots (dest) opcode
    (let ((true-dest (+ dest (pcf2-state-baseptr state)))
          )
      (if *debug-output*
          (format *error-output* "~&mkptr: ~A -> ~A~%" (get-state-val state true-dest) (+ (get-state-val state true-dest) (pcf2-state-baseptr state)))
          )
      (setf (gethash true-dest *ptrs*) t)
      (set-state-val state true-dest
                     (+ (pcf2-state-baseptr state) (get-state-val state true-dest))
                     )
      )
    )
  )

(defmethod-ut run-opcode ((state pcf2-state) (opcode gate))
  (with-slots (dest op1 op2 truth-table) opcode
    (declare (optimize (debug 3) (speed 0)))
    (let ((true-op1 (+ op1 (pcf2-state-baseptr state)))
          (true-op2 (+ op2 (pcf2-state-baseptr state)))
          (true-dest (+ dest (pcf2-state-baseptr state)))
          )
      (let ((op1val (get-state-val state true-op1))
            (op2val (get-state-val state true-op2))
            )
        (let ((op1val (etypecase op1val
                        (bit op1val)
                        (input-bit (input-bit-val op1val))
                        )
                )
              (op2val (etypecase op2val
                        (bit op2val)
                        (input-bit (input-bit-val op2val))
                        )
                )
              (rval (if (or (typep op1val 'input-bit) (typep op2val 'input-bit))
                        0
                        1))
              )
          (let ((state (ecase rval
                         (0 (if (equalp truth-table #*0110)
                                (incf-xor state)
                                (incf-non-xor state)
                                )
                            )
                         (1 state)
                         )
                  )
                )
            (declare (type bit op1val op2val))
            (set-state-val state true-dest
                           (ecase rval
                             (1 (bit truth-table (+ op1val (* 2 op2val))))
                             (0 (make-input-bit :val (bit truth-table (+ op1val (* 2 op2val)))))
                             )
                           )
            )
          )
        )
      )
    )
  :tests
  ((xor-works . (lambda ()
                  (and
                   (with-input-from-string (in-stream "0
0")
                     (let* ((op (make-instance 'gate :dest 2 :op1 0 :op2 1 :truth-table #*0110))
                            (state (init-state 10 (list op) in-stream 0 0))
                            )
                       (setf state (set-state-val state 1 1))
                       (setf state (set-state-val state 2 0))
                       (setf state (run-opcode state op))
                       (= (get-state-val state 3) 1)
                       )
                     )
                   )
                   (with-input-from-string (in-stream "0
0")
                     (let* ((op (make-instance 'gate :dest 2 :op1 0 :op2 1 :truth-table #*0110))
                            (state (init-state 10 (list op) in-stream 0 0))
                            )
                       (setf state (set-state-val state 1 1))
                       (setf state (set-state-val state 2 1))
                       (setf state (run-opcode state op))
                       (= (get-state-val state 3) 0)
                       )
                     )
                   (with-input-from-string (in-stream "0
0")
                     (let* ((op (make-instance 'gate :dest 2 :op1 0 :op2 1 :truth-table #*0110))
                            (state (init-state 10 (list op) in-stream 0 0))
                            )
                       (setf state (set-state-val state 1 0))
                       (setf state (set-state-val state 2 1))
                       (setf state (run-opcode state op))
                       (= (get-state-val state 3) 1)
                       )
                     )
                   )
              )
   (only-dest-changed .
                      (lambda ()
                        (declare (optimize (debug 3)))
                        (with-input-from-string (in-stream "0
0")
                          (let* ((op (make-instance 'gate :dest 2 :op1 0 :op2 1 :truth-table #*0110))
                                 (state (init-state 10 (list op) in-stream 0 0))
                                 )
                            (setf state (set-state-val state 1 0))
                            (setf state (set-state-val state 2 1))
                            (let ((res t)
                                  (saved-state (copy-seq (pcf2-state-memory state)))
                                  )
                              (setf state (run-opcode state op))
                              (loop for i from 0 to (1- (length (pcf2-state-memory state)))
                                 unless (= 3 i)
                                 do
                                   (setf res (and res (= (aref (pcf2-state-memory state) i)
                                                         (aref saved-state i)
                                                         )
                                                  )
                                         )
                                   )
                              res
                              )
                            )
                          )
                        )
                      )
   (and-works . (lambda ()
                  (and
                   (with-input-from-string (in-stream "0
0")
                     (let* ((op (make-instance 'gate :dest 2 :op1 0 :op2 1 :truth-table #*0001))
                            (state (init-state 10 (list op) in-stream 0 0))
                            )
                       (setf state (set-state-val state 1 1))
                       (setf state (set-state-val state 2 0))
                       (setf state (run-opcode state op))
                       (= (get-state-val state 3) 0)
                       )
                     )
                   )
                   (with-input-from-string (in-stream "0
0")
                     (let* ((op (make-instance 'gate :dest 2 :op1 0 :op2 1 :truth-table #*0001))
                            (state (init-state 10 (list op) in-stream 0 0))
                            )
                       (setf state (set-state-val state 1 1))
                       (setf state (set-state-val state 2 1))
                       (setf state (run-opcode state op))
                       (= (get-state-val state 3) 1)
                       )
                     )
                   (with-input-from-string (in-stream "0
0")
                     (let* ((op (make-instance 'gate :dest 2 :op1 0 :op2 1 :truth-table #*0001))
                            (state (init-state 10 (list op) in-stream 0 0))
                            )
                       (setf state (set-state-val state 1 0))
                       (setf state (set-state-val state 2 1))
                       (setf state (run-opcode state op))
                       (= (get-state-val state 3) 0)
                       )
                     )
                   )
              ) 
   )
  )

(defmethod run-opcode ((state pcf2-state) (opcode label))
;  (format t "label ~A cnd ~A~%" (slot-value opcode 'str) (get-state-val state 0))
  state
  )
