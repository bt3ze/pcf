;; Dataflow analysis framework for PCF2 bytecode. We use this to eliminate unnecessary gates that don't contribute to the output

(defpackage :pcf2-dataflow
  (:use :common-lisp :pcf2-bc :setmap :utils)
  (:export make-pcf-cfg
           pcf-basic-block
           get-cfg-top
           get-label-map
           get-next-blocks
           get-prev-blocks
           get-block-op
           get-block-succs
           get-block-preds
           get-block-out-set
           get-block-id
           get-block-by-id
           flow-test
           *lattice-top*)
  )
(in-package :pcf2-dataflow)


;; these special functions are included by the PCF interpreters and therefore will not have lookups in the .PCF2 file
;; alice and bob return unsigned integers
;; output_alice and output_bob give outputs to the parties
(defparameter *specialfunctions* (set-from-list (list "alice" "bob" "output_alice" "output_bob") :comp #'string<))
(defparameter *lattice-top* -1)
;;;
;;; the pcf-basic-block struct 
;;; and supporting macros
;;;

(defstruct (pcf-graph
             (:print-function
              (lambda (struct stream depth)
                (declare (ignore depth))
                (format stream "~&PCF2 CFG Block Bottom ~A:~%" (get-graph-bottom struct))
                (format stream "~&PCF2 CFG Block Map ~A:~%" (get-graph-map struct)))))
  (cfg (map-empty :comp #'<) :type avl-set)
  (bottom nil)
  )

(defun get-graph-map (cfg)
  (pcf-graph-cfg cfg)
  )

(defun get-graph-bottom (cfg)
  (pcf-graph-bottom cfg)
  )

(defmacro graph-insert (key val cfg)
  `(make-pcf-graph
    :cfg (map-insert ,key ,val (get-graph-map ,cfg))
    :bottom (get-graph-bottom ,cfg)
    ))                  

(defmacro new-cfg (&key (cfg `(map-empty :comp #'<)) (bottom nil))
  `(make-pcf-graph
    :cfg ,cfg
    :bottom ,bottom)
  )

(defmacro cfg-with-bottom (&key cfg bottom)
  `(make-pcf-graph
    :cfg (get-graph-map ,cfg)
    :bottom ,bottom))

(defmacro cfg-with-map (&key cfg map)
  `(make-pcf-graph
    :cfg ,map
    :bottom (get-graph-bottom ,cfg)))

(defstruct (pcf-basic-block
             (:print-function
              (lambda (struct stream depth)
                (declare (ignore depth))
                (format stream "~&PCF2 basic block ~A:~%" (get-block-id struct))
                (format stream "Op: ~A~%" (get-block-op struct))
                (format stream "Preds: ~A~%" (get-block-preds struct))
                (format stream "Succs: ~A~%" (get-block-succs struct))
                (format stream "Out-Set: ~A~%" (get-block-out-set struct))
                
                )
              )
             )
  (id)
  (op nil :type list)
  (preds nil :type list)
  (succs nil :type list)
  (out-set (empty-set) :type avl-set)
  (data nil :type list)
  (:documentation "This represents a basic block in the control flow graph.")
  )


(defun get-block-id (blck)
  (pcf-basic-block-id blck))
#|
(defmacro get-block-id (blck)
  (let ((blocksym (gensym)))
    `(let ((,blocksym ,blck))
       (pcf-basic-block-id ,blocksym))))
|#

(defun get-block-preds (blck)
  (pcf-basic-block-preds blck))

(defun get-block-succs (blck)
  (pcf-basic-block-succs blck))

(defun get-block-op-list (blck)
  (pcf-basic-block-op blck))
  
(defun get-block-op (blck)
  (car (get-block-op-list blck)))

(defun get-block-out-set (blck)
  (pcf-basic-block-out-set blck))

(defmacro get-block-data (blck)
  (let ((blocksym (gensym)))
    `(let ((,blocksym ,blck))
       (pcf-basic-block-data ,blocksym))))

(defmacro get-idx-by-label (targ lbls)
  `(cdr (map-find ,targ ,lbls)))

(defmacro get-block-by-id (id blocks)
  `(cdr (map-find ,id (get-graph-map ,blocks))))


(defmacro new-block (&key id op)
  `(make-pcf-basic-block
   :id ,id
   :op (list ,op)))

;; op is an opcode, bb is the block itself
(defmacro add-op (op bb &body body)
  `(let ((,bb (make-pcf-basic-block
               :id (get-block-id ,bb)
               :op (cons ,op (get-block-op-list ,bb))
               :preds (get-block-preds ,bb)
               :succs (get-block-succs ,bb)
               :out-set (get-block-out-set ,bb)
               )))
     ,@body))

;; prd is an index, bb is the block itself
(defmacro add-pred (prd bb &body body)
  `(let ((,bb (make-pcf-basic-block
               :id (get-block-id ,bb)
               :op (get-block-op-list ,bb)
               :preds (cons ,prd (get-block-preds ,bb))
               :succs (get-block-succs ,bb)
               :out-set (get-block-out-set ,bb)
               )))
     ,@body))

(defmacro set-block-preds (prds bb &body body)
  `(let ((,bb (make-pcf-basic-block
               :id (get-block-id ,bb)
               :op (get-block-op-list ,bb)
               :preds ,prds
               :succs (get-block-succs ,bb)
               :out-set (get-block-out-set ,bb)
               )))
     ,@body))

;; succ is an index, bb is the block itself
(defmacro add-succ (succ bb &body body)
  `(let ((,bb (make-pcf-basic-block
               :id (get-block-id ,bb)
               :op (get-block-op-list ,bb)
               :preds (get-block-preds ,bb)
               :succs (cons ,succ (get-block-succs ,bb))
               :out-set (get-block-out-set ,bb)
               )))
     ,@body))

(defmacro set-block-succs (succs bb &body body)
  `(let ((,bb (make-pcf-basic-block
               :id (get-block-id ,bb)
               :op (get-block-op-list ,bb)
               :preds (get-block-succs ,bb)
               :succs ,succs
               :out-set (get-block-out-set ,bb)
               )))
     ,@body))

;; not sure which of the two following I will use
;; new-set is the new out-set
(defmacro set-out-set (new-set bb &body body)
  `(let ((,bb (make-pcf-basic-block
               :id (get-block-id ,bb)
               :op (get-block-op-list ,bb)
               :preds (get-block-preds ,bb)
               :succs (get-block-succs ,bb)
               :out-set ,new-set
               )))
     ,@body))

(defmacro set-out-to-top (bb)
  `(set-out-set (empty-set) ,bb
     ,bb))

;; new-set is the new out-set
(defmacro update-out-set (new-set join-fn bb &body body)
  `(let ((,bb (make-pcf-basic-block
               :id (get-block-id ,bb)
               :op (get-block-op-list ,bb)
               :preds (get-block-preds ,bb)
               :succs (get-block-succs ,bb)
               :out-set (funcall ,join-fn ,new-set (get-block-out-set ,bb))
               )))
     ,@body))

;; id should be an integer
;; val should be a block
;; blocks should be the map of blocks
(defmacro insert-block (id val blocks &body body)
  ;;  `(let ((,blocks (map-insert (write-to-string ,id) ,val ,blocks)))
  ;;     ,@body))
  `(let ((,blocks (graph-insert ,id ,val ,blocks)))
     ,@body))

;;;
;;;
;;; cfg-basic-block functions that instruct how to behave when building the cfg and encountering all of the possible ops
;;;
;;;


(defgeneric cfg-basic-block (next-op cur-op blocks lbls fns idx callstack)
  (:documentation "update the entities in the cfg for each op that we encounter from ops")
  ;; blocks is a map of all idx to basic blocks
  ;; lbls is a map of all of the label names to idxs
  ;; fns is the set of function names
  ;; idx is the index of current op
  )

;; this one catches all the stuff i don't define. it performs a standard operation.
(defmacro add-standard-block () ; next-op cur-op blocks lbls fns idx
  `(let ((newblock (new-block :id idx :op cur-op)))
     (add-succ (1+ idx) newblock
         (close-add-block))))

(defmacro close-add-block ()
  `(insert-block idx newblock blocks
                 (list next-op
                       blocks
                       lbls
                       fns
                       (1+ idx)
                       callstack)))

(defmethod cfg-basic-block (next-op (cur-op instruction) blocks lbls fns idx callstack)
  (add-standard-block))

(defmacro definstr (type &body body)
  "PCF instruction processing methods are defined with this macro.  It is a convenience macro that ensures that the method takes the right number of arguments."
  `(defmethod cfg-basic-block ((next-op instruction) (cur-op ,type) blocks lbls fns idx callstack)
     (declare (optimize (debug 3) (speed 0)))
     (aif (locally ,@body)
          it
          (add-standard-block)
          )))

(defmacro initbase-instr ()
  `(let ((newblock (new-block :id idx :op cur-op)))
     ;; this one's successor is ALWAYS main
     (add-succ (get-idx-by-label "main" lbls) newblock
         (close-add-block))))

(definstr initbase
  (initbase-instr))

#|
;; the following defmethod shouldn't really be necessary because it's covered by two other defmethods, but this is here for clarity
(defmethod cfg-basic-block (next-op (cur-op initbase) blocks lbls fns idx callstack)
  (initbase-instr))
|#

(defmacro ret-instr ()
  `(let ((newblock (new-block :id idx :op cur-op)))
    (close-add-block)))
;; successors are added after the initial cfg is built using the call/ret maps

(definstr ret
  (ret-instr))

(definstr call
  (with-slots (fname) cur-op
    (cond
      ((set-member fname *specialfunctions*)
       (add-standard-block))
      (t (let ((newblock (new-block :id idx :op cur-op)))
            (add-succ (1+ idx) newblock
                (add-succ (get-idx-by-label fname lbls) newblock
                    (close-add-block))))))))


(defmacro branch-instr ()
  `(with-slots (targ) cur-op
     (let ((newblock (new-block :id idx :op cur-op)))
       (add-succ (1+ idx) newblock
           (add-succ (get-idx-by-label targ lbls) newblock
               (close-add-block))))))

(definstr branch
  (branch-instr))

(defmethod cfg-basic-block ((next-op label) (cur-op instruction) blocks lbls fns idx callstack)
  (declare (optimize (debug 3)(speed 0)))
  (with-slots (str) next-op
    (cond
      ((set-member str fns) ;; if we're about to declare a function, it doesn't get added as a successor right now. main is preceded by initbase and functions will get their successors from the call instruction 
       (typecase cur-op
         (initbase (initbase-instr))
         (t
          (let ((newblock (new-block :id idx :op cur-op)))
            (format t "~A~%" newblock)
            (format t "~A~%" next-op)
            (close-add-block))))) 
      (t 
       (typecase cur-op
         ;; not every instruction can be followed by "label," so here we identify the important things that some might have to do
         (branch (branch-instr))
         (initbase (initbase-instr))
         (ret (ret-instr))
         (t (add-standard-block)))))))

;;;
;;; constructing and operating on the cfg
;;;


(defun get-cfg-top (cfg)
  (declare (ignore cfg))
  0)

;  (get-idx-by-label "pcfentry" cfg) cfg)

(defun get-cfg-bottom (cfg)
  ;; need the index of the very last node in the cfg, which is the return from "main"
  (get-graph-bottom cfg)
  )

(defun get-prev-blocks (block cfg)
  (mapc
   (lambda (b) (get-block-by-id b cfg))
   (get-block-preds block)))

(defun get-next-blocks (block cfg)
  (mapc
   (lambda (b) (get-block-by-id b cfg))
   (get-block-succs block)))


(defun get-label-and-fn-map (ops)
  ;; iterate through all of the ops; when hit a label, insert its (name->idx) pair into lbls
  ;; also get the names of all of the functions (other than main) that are called
  ;; ret-addrs will contain the return addresses of all of the functions {(fname)->(return-address)}
  ;; call-addrs will contain addresses where each function is called { (addr)->(fname)}
  (reduce #'(lambda(y op)
                     (declare (optimize (debug 3) (speed 0)))
                     (let ((lbls (first y))
			   (fns (second y))
                           (idx (third y))
                           (ret-addrs (fourth y))
                           (callstack (fifth y))
                           (call-addrs (sixth y)))
                       (typecase op
                         (label 
                          (with-slots (str) op
                            (if (or (equalp (subseq str 0 1) "$")
                                    (equalp str "pcfentry")) ;; main can be included here because it returns;
                                (list 
                                 (map-insert str idx lbls)
                                 fns
                                 (+ 1 idx)
                                 ret-addrs
                                 callstack
                                 call-addrs) ;; we have a regular label
                                (list
                                 (map-insert str idx lbls)
                                 fns
                                 (+ 1 idx)
                                 ret-addrs ;; some function whose ret address should be known
                                 (cons str callstack)
                                 call-addrs ))))
			 (call (with-slots (fname) op
				 (list lbls
                                       (set-insert fns fname)
                                       (+ 1 idx)
                                       ret-addrs
                                       callstack
                                       (if (set-member fname *specialfunctions*)
                                           call-addrs
                                           (map-insert idx fname call-addrs)))))
                         (ret (list lbls
                                    fns
                                    (+ 1 idx)
                                    (map-insert (car callstack) idx ret-addrs)
                                    (cdr callstack)
                                    call-addrs))
                         (t (list lbls fns (+ 1 idx) ret-addrs callstack call-addrs)))))
          ops
          :initial-value (list (map-empty :comp #'string<)
                               (empty-set :comp #'string<)
                               0
                               (map-empty :comp #'string<)
                               nil
                               (map-empty :comp #'<))))


(defun find-preds (f-cfg)
  (declare (optimize (debug 3) (speed 0)))
  ;;(print "find preds")
  ;; for every item in blocks, get its successors and update those to identify a predecessor
  (map-reduce #'(lambda(cfg blockid blck) 
		  (reduce (lambda (cfg* succ)
			    (declare (optimize (debug 3)(speed 0)))
                            (let ((updateblock (get-block-by-id succ cfg*))
				  ;; (blockid (parse-integer blockid)
                                  )
			      (add-pred blockid updateblock
                                  (insert-block (get-block-id updateblock) updateblock cfg*
                                    cfg*))))
			  (get-block-succs blck) ; for each successor, add the pred
		 	  :initial-value cfg))
	      (get-graph-map f-cfg) ;map
	      f-cfg ;state
	      ))

(defun update-ret-succs (f-cfg call-addrs ret-addrs)
  ;; reduce over all the calling addresses in the cfg to update their return addresses. 1:1 map of call to return addresses
  (declare (optimize (debug 3)(speed 0)))
  ;;(print "update-ret-succs")
  ;;(print call-addrs)
  (first (map-reduce #'(lambda (state address fname)
                         (let ((cfg (first state))
                               (call-addrs (second state))
                               (ret-addrs (third state)))
                           (let ((retblock (get-block-by-id (get-idx-by-label fname ret-addrs) cfg)))
                             (add-succ (1+ address) retblock
                                 (insert-block (get-block-id retblock) retblock cfg
                                   (list
                                    cfg
                                    call-addrs
                                    ret-addrs))))))
                     call-addrs
                     (list f-cfg call-addrs ret-addrs))))


(defun make-pcf-cfg (ops)
  (declare (optimize (debug 3) (speed 0)))
  (let ((op1 (first ops))
        (restops (rest ops))
	(lbl-fn-map (get-label-and-fn-map ops)))
    ;;(print lbl-fn-map)
    (let* ((reduce-forward
            (reduce #'(lambda(x y)
                        (declare (optimize (debug 3)(speed 0)))
                        (apply #'cfg-basic-block (cons y x)))
                    restops
                    :initial-value (list op1
					 (new-cfg) ;(map-empty :comp #'string<) 
					 (first lbl-fn-map)
					 (second lbl-fn-map)
					 0
                                         nil)))
           (blocks (second reduce-forward))
           (forward-cfg
            (insert-block 
                (fifth reduce-forward) ;id
                (new-block :id (fifth reduce-forward) :op (first reduce-forward))
                blocks
              blocks))
           (cfg-bottom (cfg-with-bottom :cfg forward-cfg :bottom (fifth reduce-forward)))
           (preds (find-preds (update-ret-succs cfg-bottom
                                                (sixth lbl-fn-map)
                                                (fourth lbl-fn-map))
                              )))
      preds
      )))
#|      
(cfg-with-map :cfg cfg-bottom :map (find-preds (update-ret-succs cfg-bottom
                                                                       (sixth lbl-fn-map)
                                                                       (fourth lbl-fn-map))))))) |#
#|
(preds (find-preds (update-ret-succs cfg-bottom
                                     (sixth lbl-fn-map)
                                     (fourth lbl-fn-map)))))
(cfg-with-map :cfg cfg-bottom :map preds)))))
|#

;; when flowing,
;; each node carries info about its own out-set
;; and updates its information using predecessors' inputs
;; then, if changed, it adds its successors to the worklist
;; flow functions should be parameterizable by method used to get successors

;; need:
;; make sure that every node is touched by the worklist at least once
;; then, pull from the worklist until it is nil, remembering to add successors every time a node's value changes

(defmacro set-weaker (set1 set2 &key comp)
  (if comp
      `(,comp ,set1 ,set2)
      `(and (not (set-subset ,set2 ,set1))
            (set-subset ,set1 ,set2))))

;; need to construct some functions for comparing out-sets with those that are just "top". Any confluence operation with "top" (conf x top) = x

(defun flow-test (ops flow-fn)
  ;;(declare (ignore flow-fn))
  (let ((cfg (init-flow-to-top (make-pcf-cfg ops))))
    (print (map-keys (get-graph-map cfg)))
    (map-fold-backward
     (lambda (cfg* key block)
       (insert-block
           key
           (set-out-set
               (funcall flow-fn block cfg* nil)
               block
             block)
           cfg*
         cfg*))
     (get-graph-map cfg)
     cfg)))

(defun init-flow-to-top (cfg)
  (new-cfg :cfg 
           (map-map 
            (lambda(key val)
              (declare (ignore key))
              (set-out-to-top val))
            (get-graph-map cfg))
           :bottom (get-cfg-bottom cfg)
           ))

(defun init-flow-values (cfg flow-fn)
  (let ((empty-cfg (init-flow-to-top cfg)))
    (map-map
     (lambda(key val)
       (declare (ignore key))
       (funcall flow-fn val (get-graph-map cfg)))
     empty-cfg)))

(defun do-flow (cfg worklist flow-fn join-fn)
  (declare (optimize (debug 3)(speed 0)))
  (if (null worklist)
      cfg ; done
      (let* ((cur-node-id (car worklist))
             (worklist (cdr worklist))
             (cur-node (get-block-by-id cur-node-id cfg))
             (new-state (reduce (lambda (state neighbor-id)
                                  (let ((worklist (first state))
                                        (cfg (second state))
                                        (flow-state (third state))
                                        (neighbor (get-block-by-id neighbor-id cfg)))
                                    ;; for each neighbor, check if the neighbor's flow information is different from its recomputation
                                    (let ((new-out (funcall join-fn
                                                            (funcall flow-fn cur-node cfg flow-state) ;; this one should be the flow function on the path from pred (neighbor) to node (cur-node)
                                                            (get-block-out-set neighbor))))
                                      (if (set-weaker new-out 
                                                      (get-block-out-set neighbor))
                                          (list (cons neighbor-id worklist)
                                                (insert-block neighbor-id (set-out-set new-out neighbor neighbor) cfg
                                                  cfg)
                                                flow-state)
                                          (list worklist cfg flow-state)))))
                                (get-block-succs cur-node) ;; get-block-succs to be replaced with a way to specify whether to get succs or preds, depending on our direction
                                :initial-value (list worklist cfg nil))))
        (do-flow (first new-state) (second new-state) join-fn flow-fn))))



#|
(defun flow-forwards (cfg join-fn flow-fn)
  (let* ((init-cfg (init-flow-values cfg))
         )
    (do-flow init-cfg worklist join-fn flow-fn)))
|#
