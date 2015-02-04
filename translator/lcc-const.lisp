;; Constant detection for LCC
;;
;; This analysis is meant to detect memory locations that are constant
;; within the scope of some function e.g. loop indices.  We will just
;; assume that these locations are not tampered with outside of the
;; function via e.g. some indirection.
;;
;; We use gen/kill sets here.  The gen set contains any locations
;; where a constant is placed; the kill set contains all locations
;; that are assigned to.  For binary operations, the result is
;; constant iff both operands are constants.
;;
;; This can be viewed as "constant propagation lite"

(defpackage :lcc-const 
  (:use :cl :utils :setmap :setmap-rle :lcc-bc :lcc-dataflow)
  (:export lcc-const-flow-fn const-dataflow-funs not-const)
  (:shadow import export)
  )
(in-package :lcc-const)

(defun constcmp (x y)
  (typecase x
    (number (typecase y
              (number (< x y))
              (symbol (if (equalp y 'glob)
                          t
                          nil))))
    (symbol (if (equalp x 'glob)
                nil
                t))))


(defun lcc-const-join-fn (x y)
  "Compute the join operation on the constant propagation lattice."
  (declare (optimize (debug 3)(speed 0)))
  (map-reduce (lambda (map key val)
                    (let ((new-val (aif (map-find key map t)
                                        (typecase val
                                          (number (typecase (cdr it)
                                                    (number (if (= val (cdr it))
                                                                val
                                                                'not-const))
                                                    (symbol (cond
                                                              ((equalp (cdr it) 'not-const)
                                                               'not-const)
                                                              ;;((equalp (cdr it) 'unknown) val)
                                                              (t (error "Bad value for (cdr it)"))))
                                                    (t (error "Bad value for it - not symbol or number"))))
                                          (symbol (if (equalp val 'not-const)
                                                      'not-const
                                                      (cdr it))))
                                        'not-const))) ;; not in both maps, so the value is unknown
                      (map-insert key new-val map))) ;; computing a join on two value maps
              x
              y)
  )

(defparameter empty-s (map-empty :comp #'constcmp))

(defun const-dataflow-funs (ops)
  "Compute the locations that store constants in this stream of
opcodes.  This returns a map that is keyed by the index of the
operation, with the set of memory locations that store constant values
as its value."
  (let ((funs (lcc-dataflow:get-function-body ops)))
    (setmap:map-map (lambda (k v)
                      (declare (ignore k))
                      (multiple-value-bind (in-set in-stack) 
                          (lcc-dataflow:flow-forwards #'lcc-const-join-fn 
                                                      #'lcc-const:lcc-const-flow-fn
                                                      (lcc-dataflow:make-cfg-single-ops v) ;; cfg
                                                      (setmap:map-empty :comp #'<) ;; in-sets
                                                      (setmap:map-empty :comp #'<) ;; in-stacks
                                                      empty-s ;; empty-set
                                                      )
                        (list in-set in-stack)))
                    funs)))


#|
(defmacro reduce-over-bb-ops (bb)
  `(reduce (lambda (&optional x y)
             (set-union (aif x x empty-s) 
                        (alist->map* y :empty-m empty-s)))
           (basic-block-ops ,bb)
           :initial-value empty-s))
|#

(defun lcc-const-flow-fn (in-set in-stack bb)
  (declare (optimize (debug 3)(speed 0)))
  (let ((op (car (basic-block-ops bb))))
    (let ((stack (get-stack op in-stack in-set))
          (gen (get-gen op in-stack))
          (kill (get-kill op in-stack)))
      (list stack (set-union gen (set-diff in-set kill))))))

(defmacro pop-and-push (sym stck)
  `(cons ,sym (cdr ,stck)))

(defmacro pop-twice (stck)
  `(cdr (cdr ,stck)))

(defmacro pop-stack (stck)
  `(cdr ,stck))

(defmacro push-stack (val stck)
  `(cons ,val ,stck))

(defgeneric get-stack (op stack valmap)
  (:documentation "get the state of the stack after flowing over an op"))
(defgeneric get-gen (op stack)
  (:documentation "get the gen set produced by flowing over an op"))
(defgeneric get-kill (op stack)
  (:documentation "get the kill set produced by flowing over an op"))
;;; (defgeneric get-vals (bb)
;;;  (:documentation "get the state of the value map after flowing over a basic block")

#|
(defmacro flow-vals (type &body body)
  `(defmethod get-vals ((bb ,type))
     (declare (optimize (debug 3)(speed 0)))
     (aif (locally ,@body)
          it
          nil)))
|#

(defmacro flow-stack (type &body body)
  `(defmethod get-stack ((op ,type) stack valmap)
     (declare (optimize (debug 3)(speed 0)))
     (aif (locally ,@body)
          it
          nil)))

(defmacro flow-gen (type &body body)
  `(defmethod get-gen ((op ,type) stack)
     (declare (optimize (debug 3)(speed 0)))
     (aif (locally ,@body)
          (alist->map* it :empty-m empty-s)
          empty-s)))

(defmacro flow-kill (type &body body)
  `(defmethod get-kill ((op ,type) stack)
     (declare (optimize (debug 3)(speed 0)))
     (aif (locally ,@body)
          (alist->map* it :empty-m empty-s)
          empty-s)))

(defmacro def-gen-kill (type &key (gen nil) (kill nil) (stck nil))
  `(progn
     (flow-stack ,type ,stck)
     (flow-gen ,type ,gen)
     (flow-kill ,type ,kill)
    ))

(def-gen-kill lcc-instruction
    :stck stack
    :gen nil
    :kill nil
    )

(def-gen-kill callu
    ;; pop the call address off the stack
    ;; and add 'not-const (usually a safe assumption)
    :stck (pop-and-push 'not-const stack)
    :gen nil
    :kill nil
    )

(def-gen-kill calli
    ;; pop the call address off the stack
    ;; and add 'not-const (usually a safe assumption)
    :stck (pop-and-push 'not-const stack)
    :gen nil
    :kill nil
    )

(def-gen-kill callv
    ;; pop the call address off the stack
    :stck (pop-stack stack)
    :gen nil
    :kill nil
    )

(def-gen-kill jumpv
    ;; pop the jump address off the stack
    :stck (pop-stack stack)
    )

(def-gen-kill addrgp
    ;; address of global 
    ;; look to the glob section
    :stck (push-stack 'glob stack)
    :gen nil
    :kill nil
    )

(def-gen-kill addrfp
    ;; address of parameter
    ;; stack gains a pointer to the args
    :stck (push-stack 'args stack)
    :gen nil
    :kill nil
    )

(def-gen-kill addrlp
    ;; address of a local
    ;; stack gains the address of a specific variable in the flow data
    ;; if the address is offset, this uses a pointer to the base of the array
    ;; the above line is a bug inserted as a quick workaround, since otherwise
    ;; it will run into "object not found in map" errors when the address
    ;; is dereferenced. looking into where the array base is assigned a value,
    ;; but till now, I have only seen 'glob in that spot, which is OK
    :stck (the (cons integer t)
            (cons
             (let ((nums (string-tokenizer:tokenize (second (slot-value op 's-args)) #\+)))
               (declare (optimize (debug 3)(speed 0)))
               (if (< (length nums) 2)
                   (parse-integer (first nums))
                   (progn
                     (print nums)
                     ;;(break)
                     (parse-integer (first nums)))))
                     ;;(reduce #'(lambda (x y) (+ x (parse-integer y))) nums :initial-value 0))))
                     ;;(parse-integer (second (slot-value op 's-args))))))
             ;; arg! this be a bug!
             stack))
    )

(def-gen-kill cnstu
    :stck (the (cons integer t)
            (cons
             (parse-integer (second (slot-value op 's-args))) stack))
    )

(def-gen-kill cnsti
    :stck (the (cons integer t)
            (cons
             (parse-integer (second (slot-value op 's-args))) stack))
    )

(def-gen-kill two-arg-instruction
    :stck (push-stack 'not-const (pop-twice stack))
    )

(def-gen-kill cmp-jump-instruction
    ;; check first two spots on stack,
    ;; push const or not-const depending on their values
    :stck (let ((o1 (first stack))
                (o2 (second stack)))
            (if (or (eql 'not-const o1)
                    (eql 'not-const o2))
                (push-stack 'not-const (pop-twice stack))
                (push-stack 'const (pop-twice stack)))))

(def-gen-kill argu
    :stck (pop-stack stack)
    )

(def-gen-kill argp
    :stck (pop-stack stack)
    )

(def-gen-kill addp
    ;; pointer addition
    ;; 
    :stck (let ((op1 (first stack))
                (op2 (second stack)))
            (push-stack
             (cond
               ((or (eql op1 'glob)
                    (eql op2 'glob)) 
                'glob)
               ((or (eql op1 'args)
                    (eql op2 'args))
                'args)
               ((or (eql op1 'not-const)
                    (eql op2 'not-const))
                'not-const)
               (t (typecase op1
                    (integer (typecase op2
                               (integer (+ op1 op2))
                               (t 'glob)))
                    (t 'const))))
                    ;;(t 'glob))))
             (pop-twice stack))))

(def-gen-kill one-arg-instruction
    :stck (let ((op (first stack)))
            (if (eql 'not-const op)
                (pop-and-push 'not-const stack)
                (pop-and-push 'const stack))))

(defmacro asgn-gen ()
  `(cond
     ((eql (first stack) 'not-const) (list (cons (second stack) 'not-const)))
     ((eql (second stack) 'glob) nil)
     ((eql (second stack) 'args) nil)
     ;;((eql (second stack) 'not-const) (error "Bad address -- address is indeterminate and not global?"))
     ((null (second stack)) nil)
     ((eql (second stack) 'not-const) nil)
     (t (list (cons (the integer (second stack)) (first stack))))))
     ;;(t (list (cons (second stack) (first stack))))))


(defmacro asgn-kill ()
  `(cond
     ((eql (second stack) 'glob) nil)
     ((eql (second stack) 'args) nil)
;;     ((eql (second stack) 'not-const) nil)
     ((null (second stack)) nil)
     ;;(t (list (cons (second stack) (first stack))))))
     (t (list (cons (the integer (second stack)) (first stack))))))

(def-gen-kill asgnu
    :stck (pop-twice stack)
    :gen (asgn-gen)
    :kill (asgn-kill)
    )

(def-gen-kill asgni
    :stck (pop-twice stack)
    :gen (asgn-gen)
    :kill (asgn-kill)
    )

(defmacro indir-stack ()
  ;; dereference a pointer that's on the stack
  ;; unknown const and globs go to glob
  ;; args go to the args section
  ;; and specific consts go to the valmap
  `(cons (cond
           ((or (eql (car stack) 'glob)
                (eql (car stack) 'const))
            'glob)
           ((eql (car stack) 'args)
            'args)
           #|((eql (car stack) 'not-const)
           'not-const)
           (t (aif (cdr (map-find (car stack) valmap t))
           it
           nil))) |#
           (t (cdr (map-find (car stack) valmap))))
         (cdr stack)))

(def-gen-kill indiru
    :stck (indir-stack))

(def-gen-kill indiri
    :stck (indir-stack))

(def-gen-kill indirp
    ;; this may be buggy -- pointer fetch is not well supported
    :stck (pop-and-push 'glob stack))

(defmacro arithmetic-shift (fn op1 op2)
  `(if (or (eql op1 'glob)(eql op2 'glob))
       (push-stack 'not-const (pop-twice stack))
       (push-stack (typecase ,op1
               (integer (typecase ,op2
                          (integer (funcall ,fn ,op1 ,op2))
                          (t 'not-const)))
               (t 'not-const))
             (pop-twice stack))))

(defmacro arithmetic-stack (fn op1 op2)
  `(if (or (eql op1 'glob)(eql op2 'glob))
       (push-stack 'not-const (pop-twice stack))
       (push-stack (typecase ,op1
               (number (typecase ,op2
                         (number (funcall ,fn ,op1 ,op2))
                         (t 'not-const)))
               (t 'not-const))
             (pop-twice stack))))

(def-gen-kill lshu
    :stck (let ((op1 (first stack))
                (op2 (second stack)))
            (arithmetic-shift #'ash op2 op1)
            ))

(def-gen-kill lshi
    :stck (let ((op1 (first stack))
                (op2 (second stack)))
            (arithmetic-shift #'ash op2 op1)    
            ))

(def-gen-kill rshu
    :stck (let ((op1 (first stack))
                (op2 (second stack)))
           (arithmetic-shift #'ash op2 (aif (numberp op1) (* -1 op1) 'not-const))
           ))

(def-gen-kill rshi
    :stck (let ((op1 (first stack))
               (op2 (second stack)))
            (arithmetic-shift #'ash op2 (aif (numberp op1) (* -1 op1) 'not-const))
            ))

(def-gen-kill addu
    :stck (let ((op1 (first stack))
                (op2 (second stack)))
           (arithmetic-stack #'+ op1 op2)
           ))

(def-gen-kill addi
    :stck (let ((op1 (first stack))
               (op2 (second stack)))
           (arithmetic-stack #'+ op1 op2)
           ))

(def-gen-kill subu
    :stck (let ((op1 (first stack))
               (op2 (second stack)))
           (arithmetic-stack #'- op2 op1)
           ))

(def-gen-kill subi
    :stck (let ((op1 (first stack))
               (op2 (second stack)))
           (arithmetic-stack #'- op2 op1)
    ))

(def-gen-kill mulu
    :stck (let ((op1 (first stack))
                (op2 (second stack)))
            (arithmetic-stack #'* op2 op1)   
  ))

(def-gen-kill muli
    :stck (let ((op1 (first stack))
               (op2 (second stack)))
            (arithmetic-stack #'* op2 op1)
            ))

(def-gen-kill divu
    :stck (let ((op1 (first stack))
               (op2 (second stack)))
            (arithmetic-stack #'/ op2 op1) 
            ))

(def-gen-kill divi
    :stck (let ((op1 (first stack))
               (op2 (second stack)))
           (arithmetic-stack #'/ op2 op1)
    ))

(def-gen-kill modu
    :stck (let ((op1 (first stack))
               (op2 (second stack)))
           (arithmetic-stack #'mod op2 op1)
           ))

(def-gen-kill modi
    :stck (let ((op1 (first stack))
               (op2 (second stack)))
           (arithmetic-stack #'mod op2 op1)
    ))

(def-gen-kill boru
    :stck (let ((op1 (first stack))
               (op2 (second stack)))
           (arithmetic-stack #'logior op2 op1)
    ))

(def-gen-kill bori
    :stck (let ((op1 (first stack))
               (op2 (second stack)))
           (arithmetic-stack #'logior op2 op1)
))

(def-gen-kill bandu
    :stck (let ((op1 (first stack))
               (op2 (second stack)))
           (arithmetic-stack #'logand op2 op1)
))

(def-gen-kill bandi
    :stck (let ((op1 (first stack))
                (op2 (second stack)))
           (arithmetic-stack #'logand op2 op1)
  ))

(def-gen-kill bxoru
    :stck (let ((op1 (first stack))
               (op2 (second stack)))
           (arithmetic-stack #'logxor op2 op1)
 ))

(def-gen-kill bxori
    :stck (let ((op1 (first stack))
                (op2 (second stack)))
            (arithmetic-stack #'logxor op2 op1)
    ))

(def-gen-kill bcomu
    :stck (let ((o1 (first stack)))
            (if (or (eql o1 'glob) (eql o1 'args))
                (cons 'not-const (cdr stack))
                (cons
                 (typecase o1
                   (number (lognot o1))
                   (symbol 'not-const)
                   (t (error "unknown item on stack")))
                 (cdr stack))))
    )

(def-gen-kill bcomi
    :stck (let ((o1 (first stack)))
            (if (or (eql o1 'glob) (eql o1 'args))
                (pop-and-push 'not-const stack)
                (pop-and-push
                 (typecase o1
                   (integer (lognot o1))
                   (symbol 'not-const)
                   (t (error "unknown item on stack")))
                 stack)))
    )

(def-gen-kill negi
    :stck (let ((o1 (first stack)))
            (if (or (eql o1 'glob) (eql o1 'args))
                (pop-and-push 'not-const stack)
                (pop-and-push
                 (typecase o1
                   (number (* -1 o1))
                   (symbol 'not-const))
                 stack)))
    )
