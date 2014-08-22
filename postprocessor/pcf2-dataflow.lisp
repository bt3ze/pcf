;; Dataflow analysis framework for PCF2 bytecode. We use this to eliminate unnecessary gates that don't contribute to the output

(defpackage :pcf2-dataflow
  (:use :common-lisp :pcf2-bc :setmap :utils)
  (:export make-pcf-cfg
           pcf-basic-block
           get-cfg-top
           get-label-map
           get-next-blocks
           get-prev-blocks)
  )
(in-package :pcf2-dataflow)

;; these special functions are included by the PCF interpreters and therefore will not have lookups in the .PCF2 file
;; alice and bob return unsigned integers
;; output_alice and output_bob give outputs to the parties
(defparameter *specialfunctions* (set-from-list (list "alice" "bob" "output_alice" "output_bob") :comp #'string<))


;;;
;;; the pcf-basic-block struct 
;;; and supporting macros
;;;

(defstruct (pcf-basic-block
             (:print-function
              (lambda (struct stream depth)
                (declare (ignore depth))
                (format stream "~&PCF2 basic block ~A:~%" (pcf-basic-block-id struct))
                (format stream "Ops: ~A~%" (pcf-basic-block-ops struct))
                (format stream "Preds: ~A~%" (pcf-basic-block-preds struct))
                (format stream "Succs: ~A~%" (pcf-basic-block-succs struct))
                (format stream "Out-Set: ~A~%" (pcf-basic-block-out-set struct))
                )
              )
             )
  (id)
  (ops nil :type list)
  (preds nil :type list)
  (succs nil :type list)
  (out-set (set-insert (empty-set) "top") :type avl-set)
  (:documentation "This represents a basic block in the control flow graph.")
  )

(defmacro get-block-id (blck)
  (let ((blocksym (gensym)))
    `(let ((,blocksym ,blck))
       (pcf-basic-block-id ,blocksym))))

(defmacro get-block-preds (blck)
  (let ((blocksym (gensym)))
    `(let ((,blocksym ,blck))
      (pcf-basic-block-preds ,blocksym))))

(defmacro get-block-succs (blck)
  (let ((blocksym (gensym)))
    `(let ((,blocksym ,blck))
       (pcf-basic-block-succs ,blocksym))))

(defmacro get-block-ops (blck)
  (let ((blocksym (gensym)))
    `(let ((,blocksym ,blck))
       (pcf-basic-block-ops ,blocksym))))

(defmacro get-block-out-set (blck)
  (let ((blocksym (gensym)))
    `(let ((,blocksym ,blck))
       (pcf-basic-block-out-set ,blocksym))))

(defmacro get-idx-by-label (targ lbls)
  `(cdr (map-find ,targ ,lbls)))

(defmacro get-block-by-id (id blocks)
  `(cdr (map-find (write-to-string ,id) ,blocks)))

(defmacro new-block (&key id op)
  `(make-pcf-basic-block
   :id (write-to-string ,id)
   :ops (list ,op)))

;; op is an opcode, bb is the block itself
(defmacro add-op (op bb &body body)
  `(let ((,bb (make-pcf-basic-block
               :id (get-block-id ,bb)
               :ops (cons ,op (get-block-ops ,bb))
               :preds (get-block-preds ,bb)
               :succs (get-block-succs ,bb)
               :out-set (get-block-out-set ,bb)
               )))
     ,@body))

;; prd is an index, bb is the block itself
(defmacro add-pred (prd bb &body body)
  `(let ((,bb (make-pcf-basic-block
               :id (get-block-id ,bb)
               :ops (get-block-ops ,bb)
               :preds (cons ,prd (get-block-preds ,bb))
               :succs (get-block-succs ,bb)
               :out-set (get-block-out-set ,bb)
               )))
     ,@body))

(defmacro set-block-preds (prds bb &body body)
  `(let ((,bb (make-pcf-basic-block
               :id (get-block-id ,bb)
               :ops (get-block-ops ,bb)
               :preds ,prds
               :succs (get-block-succs ,bb)
               :out-set (get-block-out-set ,bb)
               )))
     ,@body))

;; succ is an index, bb is the block itself
(defmacro add-succ (succ bb &body body)
  `(let ((,bb (make-pcf-basic-block
               :id (get-block-id ,bb)
               :ops (get-block-ops ,bb)
               :preds (get-block-preds ,bb)
               :succs (cons ,succ (get-block-succs ,bb))
               :out-set (get-block-out-set ,bb)
               )))
     ,@body))

(defmacro set-block-succs (succs bb &body body)
  `(let ((,bb (make-pcf-basic-block
               :id (get-block-id ,bb)
               :ops (get-block-ops ,bb)
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
               :ops (get-block-ops ,bb)
               :preds (get-block-preds ,bb)
               :succs (get-block-succs ,bb)
               :out-set ,new-set
               )))
     ,@body))

;; new-set is the new out-set
(defmacro update-out-set (new-set join-fn bb &body body)
  `(let ((,bb (make-pcf-basic-block
               :id (get-block-id ,bb)
               :ops (get-block-ops ,bb)
               :preds (get-block-preds ,bb)
               :succs (get-block-succs ,bb)
               :out-set (funcall ,join-fn ,new-set (get-block-out-set ,bb))
               )))
     ,@body))

(defmacro push-stack (val stack &body body)
  `(let ((,stack (cons ,val stack)))
     ,@body))

(defmacro pop-stack (val stack &body body)
  `(let ((,val (car ,stack))
         (,stack (cdr ,stack)))
     ,@body))


;; id should be an integer
;; val should be a block
;; blocks should be the map of blocks
(defmacro insert-block (id val blocks &body body)
  `(let ((,blocks (map-insert (write-to-string ,id) ,val ,blocks)))
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
      ((set-member str fns) ;; if we're about to declare a function, it doesn't get added as a successor right now. main is preceded by initbase (this is handled elsewhere, and main isn't even in "fns" anyway) and functions will get their successors from the call instruction 
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
  0)

;  (get-idx-by-label "pcfentry" cfg) cfg)

(defun get-cfg-bottom (cfg)
  ;; need the index of the very last node in the cfg, which is the return from "main"
  ;; is there an efficient way to get this?
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
                                           (map-insert (write-to-string idx) fname call-addrs)))))
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
                               (map-empty :comp #'string<))))


(defun find-preds (f-cfg)
  (declare (optimize (debug 3) (speed 0)))
  ;; for every item in blocks, get its successors and update those to identify a predecessor
  (map-reduce #'(lambda(cfg blockid blck) 
		  (reduce (lambda (cfg* succ)
			    (declare (optimize (debug 3)(speed 0)))
                            (let ((updateblock (get-block-by-id succ cfg*))
				  (blockid (parse-integer blockid))
                                  )
			      (add-pred blockid updateblock
                                  (insert-block (parse-integer (get-block-id updateblock)) updateblock cfg*
                                    cfg*))))
			  (get-block-succs blck) ; for each successor, add the pred
		 	  :initial-value cfg))
	      f-cfg ;map
	      f-cfg ;state
	      ))

(defun update-ret-succs (f-cfg call-addrs ret-addrs)
  ;; reduce over all the calling addresses in the cfg to update their return addresses. 1:1 map of call to return addresses
  (declare (optimize (debug 3)(speed 0)))
  (print call-addrs)
  (first (map-reduce #'(lambda (state address fname)
                         (let ((cfg (first state))
                               (call-addrs (second state))
                               (ret-addrs (third state)))
                           (let ((retblock (get-block-by-id (get-idx-by-label fname ret-addrs) cfg)))
                             (add-succ (1+ (parse-integer address)) retblock
                                 (insert-block (parse-integer (get-block-id retblock)) retblock cfg
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
    (print lbl-fn-map)
    (let* ((reduce-forward
            (reduce #'(lambda(x y)
                        ;; (break)
                        (declare (optimize (debug 3)(speed 0)))
                        (apply #'cfg-basic-block (cons y x)))
                    restops
                    :initial-value (list op1
					 (map-empty :comp #'string<) 
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
              blocks)));      forward-cfg
      (print *specialfunctions*)
      (let ((preds (find-preds (update-ret-succs forward-cfg
                                     (sixth lbl-fn-map)
                                     (fourth lbl-fn-map)))))
        (print "got preds")
        (progn
          (loop for i from 0 to 25
             collect (print (get-block-by-id i preds)))
          (circuit-topo-sort preds))
        ;preds
        ))))
  
  
(defun recursive-list (limit cur)
  (if (eq cur limit)
      cur
      (cons cur (recursive-list limit (1+ cur)) )))

;;; circuit topological sort - use the cfg to determine a topological ordering of nodes for visiting
#|
(defun circuit-topo-sort (cfg)
  ;;(declare (optimize (debug 3)(speed 0)))
  (labels ((visit (node-id cfg sorted-list)
             ;;(break)
             (if (null node-id)
                 sorted-list ; done
                 (let ((node (get-block-by-id node-id cfg)))
                   (reduce (lambda (topo-list neighbor-id)
                             (let ((neighbor (get-block-by-id neighbor-id cfg)))
                               (set-block-preds (remove node-id (get-block-preds neighbor)) neighbor
                                 ;;(set-block-succs (remove neighbor-id (get-block-succs node)) node
                                   (insert-block neighbor-id neighbor cfg 
                                     (if (null (get-block-preds neighbor))
                                         (progn (print neighbor-id)
                                                (cons neighbor-id (visit neighbor-id cfg topo-list)))
                                         topo-list)))))
                           ;;)
                           (get-block-succs node)
                           :initial-value sorted-list 
                           )))))
    ;; (recursive-list 15000 0) ))
    (cons 0 (visit (get-cfg-top cfg) cfg nil))))
|#

;; when flowing,
;; each node carries info about its own out-set
;; and updates its information using predecessors' inputs
;; then, if changed, it adds its successors to the worklist
;; flow functions should be parameterizable by method used to get successors

;; need:
;; make sure that every node is touched by the worklist at least once
;; (perhaps reduce on every node in the cfg -- or some method that follows all of the successors/predecessors (whichever method we're using) once -- DFS should work for this for postorder/reverse postorder)
;; then, pull from the worklist until it is nil, remembering to add successors every time a node's value changes


(defmacro set-weaker (set1 set2 &key comp)
  (if comp
      `(,comp ,set1 ,set2)
      `(and (not (set-subset ,set2 ,set1))
            (set-subset ,set1 ,set2))))

;; need to construct some functions for comparing out-sets with those that are just "top". Any meet(top, set-x) = set-x; and any join(top, set-x) is set-x


(defun do-flow (cfg worklist join-fn flow-fn)
  (declare (optimize (debug 3)(speed 0)))
  (if (null worklist)
      cfg ; done
      (let* ((cur-node-id (car worklist))
             (worklist (cdr worklist))
             (cur-node (get-block-by-id cur-node-id cfg))
             (new-state (reduce (lambda (state neighbor-id)
                                  (let ((worklist (first state))
                                        (cfg (second state))
                                        (neighbor (get-block-by-id neighbor-id cfg)))
                                    ;; for each neighbor, check if the neighbor's flow information is different from its recomputation
                                    (let ((new-out (funcall join-fn
                                                            (flow-fn (get-block-out-set cur-node)) ;; this one should be the flow function on the path from pred (neighbor) to node (cur-node)
                                                            (get-block-out-set neighbor))))
                                      (if (set-weaker new-out 
                                                      (get-block-out-set neighbor))
                                          (list (cons neighbor-id worklist)
                                                (map-insert neighbor-id 
                                                            (set-out-set new-out neighbor
                                                              neighbor)
                                                            cfg))
                                          (list worklist cfg)))))
                                (get-block-succs cur-node) ;; get-block-succs to be replaced with a way to specify whether to get succs or preds, depending on our direction
                                :initial-value (list worklist cfg))))
        (do-flow (first new-state) (second new-state) join-fn flow-fn))))



(defun flow-forwards (cfg join-fn flow-fn)
  (let* ((init-cfg ;; this first map-reduce will give us a worklist we can work with and an initialized set of blocks
          (map-reduce (lambda (state blockid blck)
                        (let ((cfg (first state))
                              (worklist (second state)))
                          (set-out-set (empty-set) blck
                            (let ((cfg (map-insert blockid blck cfg)))
                              (list cfg worklist)))))
                      cfg ;; reduce over cfg
                      (list cfg nil) ;; init-state
                      ))
         (cfg* (first init-cfg))
         (worklist (second init-cfg))
         )
    (do-flow cfg* worklist join-fn flow-fn)))
