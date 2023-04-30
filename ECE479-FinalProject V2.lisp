#|

	ECE 479 Final Project
	Jonah Goetze
	Thomas Milbauer

	Written in Proof Pad

	Note: The entire project is in this single file. We had issues certifying and importing books. We believe it is a Proof Pad bug. 
	Note: :trans1 would generate errors in Proof Pad. Those were done in the online version of Proof Pad, http://new.proofpad.org/ , results pasted here

|#

; --------------- 11.5 ----------------

; Definitions copied from textbook page 193, 194

; Prove (perm x x)

(defun in (a b)
  (cond ((atom b) nil)
        ((equal a (car b)) t)
        (t (in a (cdr b)))))

(defun del (a x)
  (cond ((atom x) nil)
        ((equal a (car x)) (cdr x))
        (t (cons (car x) (del a (cdr x))))))

(defun perm (x y)
  (cond ((atom x) (atom y))
        (t (and (in (car x) y)
                (perm (cdr x) (del (car x) y))))))

 ; Prove (implies (perm x y) (perm y x))

(defthm perm-Reflexive-Property
         (perm x x))

 (encapsulate ()
  (defthm perm-del
     (implies (in a y)
              (equal (perm y (cons a x))
                     (perm (del a y) x)))
            
  
 ; The only way I could get this to work is with this hint..
 ; we got help with this part
     :hints (("Goal" :induct (perm y x)))))

; Prove (implies (and (perm x y) (perm y z)) (perm x z))

    ;x + y = y + x
(defthm perm-Symmetric-Property
    (implies (perm x y) (perm y x)))
	
	; x - a + y = x + y
(defthm in-del
         (implies (in x (del a y))
                  (in x y)))

	;x1 in y but not z, y z cannot contain the exact same elements
(defthm perm-in-same
(implies (and (not (in x1 z))
              (in x1 y))
         (not (perm y z))))
	
	;x - a - b = x - b - a
(defthm del2
         (equal (del a (del b x))
                (del b (del a x))))

	;a - b + y = a + y
(defthm in-del3
         (implies (not (equal a b))
                  (equal (in a (del b y))
                         (in a y))))

	;if a is in y and z, y and z must be perms
	; if removing a from y and z are perms of each other still
(defthm perm-del2
         (implies (and (in a y)
                       (in a z))
                  (equal (perm y z)
                         (perm (del a y) (del a z)))))

	; if x y are perm, and y z are perm, x z must be perm
	; x=y y=z so x=z
(defthm perm-Substitution-Property
         (implies (and (perm x y) (perm y z)) (perm x z)))

(defequiv perm)


#|
trans1 only seems to work on the online version of proofpad 

:trans1 (defequiv perm)
(DEFTHM PERM-IS(-AN-EQUIVALENCE
         (AND (BOOLEANP (PERM X Y))
              (PERM X X)
              (IMPLIES (PERM X Y) (PERM Y X))
              (IMPLIES (AND (PERM X Y) (PERM Y Z))
                       (PERM X Z)))
         :RULE-CLASSES (:EQUIVALENCE))

|#

; --------------- 11.6 ----------------

#|
:trans1(defcong perm perm (append x y) 1)
(DEFTHM PERM-IMPLIES-PERM-APPEND-1
         (IMPLIES (PERM X X-EQUIV)
                  (PERM (APPEND X Y) (APPEND X-EQUIV Y)))
         :RULE-CLASSES (:CONGRUENCE))
|#

; --------------- 11.7 ----------------

	; a is an element of x, a is concatenation of x if a is only in y
	(defthm in-concat
  		(equal (in a (append x y))
       	  (or (in a x) (in a y))))


	;same as in-concat but for removing a 

(defthm del-concat
   (equal (del a (append x y))
         (if (in a x)
             (append (del a x) y)
           (append x (del a y)))))

(defcong perm perm (append x y) 1))
(defcong perm perm (append x y) 2))

; --------------- 11.8 ----------------

	;returns all elements in lst less than x
(defun less (x lst)
  	(cond ((atom lst) nil)
	((< (car lst) x)
	 (cons (car lst) (less x (cdr lst))))
	(t (less x (cdr lst)))))

; --------------- 11.9 ----------------

	;returns all elements in lst not less than x
(defun notless (x lst)
  	(cond ((endp lst) nil)
      ((< (car lst) x)
       (notless x (cdr lst)))
      (t (cons (car lst) (notless x (cdr lst))))))

; --------------- 11.10 ---------------
	
	;definition from textbook
(defun qsort (x)
   (cond ((atom x) nil)
         (t (append (qsort (less (car x) (cdr x)))
                    (list (car x))
                    (qsort (notless (car x) (cdr x)))))))

	;says it does not matter which order you add variable a
(defthm perm-cons
	(perm (append x (cons a y)) (cons a (append x y))))

	;if we take elements in x2 that are less than x1, concat them with x1 and then concat the rest with x2,
	;result will be a perm of x1 and x2 in proper order
(defthm perm-append-less-notless
	(perm (append (less x1 x2)
           	(cons x1 (notless x1 x2)))
           (cons x1 x2)))

(defthm perm-qsort
   (perm (qsort x) x))

; --------------- 11.11 ---------------

	;checks if every ekement in lst is less than x
(defun lessp (x lst)
  (if (endp lst)
      t
  (and (< (car lst) x)
      (lessp x (cdr lst)))))

; --------------- 11.12 ---------------

	;checks if every element in x is greater than x
(defun notlessp (x lst)
  (if (endp lst)
      t
  (and (not (< (car lst) x))
      (notlessp x (cdr lst)))))

; --------------- 11.13 ---------------

	;returns t if the list is sorted in an increasing order
(defun orderedp (lst)
	(if (or (endp lst) (endp (cdr lst)))
     	t
     (and (<= (car lst) (cadr lst))
          (orderedp (cdr lst)))))

	;if x and y are ordered, and all of x is smaller than y, appending x and y is also ordered
(defthm ordered-append
	(equal (orderedp (append x y))
     	(if (consp x)
             (if (consp y)
             	(and (orderedp x)
               	(orderedp y)
                    	(<= (car (last x)) (car y)))
               	(orderedp x))
           		(orderedp y))))

(defcong perm equal (lessp x lst) 2)

(defcong perm equal (notlessp x lst) 2)

; --------------- 11.14 ---------------

	;if lst is not less than a, create a sublist with elements not less than a
(defthm notlessp-notless
	(notlessp a (notless a lst)))

	;opposite of notlessp-notless
(defthm lessp-less
	(lessp a (less a lst)))

	;if a is not less than or equal to all elements in lst, and x is a member of lst, then x is not less than a
(defthm notlessp2
	(implies (and (notlessp a lst)
                (member x lst))
           (not (< x a))))

	;;if a is less than or equal to all elements in lst, and x is a member of lst, then x is less than a
(defthm lessp2
	(implies (and (lessp a lst)
     	(member x lst))
          	(< x a)))

	;if a is greater than the first element of lst, it must also be greater than every other element in the list
(defthm notlessp3
	(implies (and (notlessp a lst)
     	(consp lst))
          	(not (< (car lst) a))))
	
	;if a is less than the first element of lst, it must also be less than every other element in the list
(defthm lessp3
	(implies (and (lessp a lst)
     	(consp lst))
          	(< (car lst) a)))

	;if a is not less than any element in lst, a is also not less than any element in qsort lst
(defthm notlessp-qsort
	(equal (notlessp a (qsort lst))
     	(notlessp a lst)))

	;if a is less than any element in lst, a is also less than any element in qsort lst
(defthm lessp-qsort
	(equal (lessp a (qsort lst))
     	(lessp a lst)))

(defthm lessp4
	(implies (and (lessp a lst)
     	(consp lst))
          	(<= (car (last lst)) a)))

	;orderedp-qsort proven
(defthm orderedp-qsort
	(orderedp (qsort lst)))

; --------------- 11.15 ---------------

	;takes a list x and splits it in half, one half is the odd elements, other is even elements
(defun split (x)
  (cond ((atom x) (mv nil nil))
	((atom (cdr x)) (mv x nil))
	(t (mv-let (a b)
		   (split (cddr x))
		   (mv (cons (car x) a) (cons (cadr x) b))))))

	;merges lists x and y. Sorts by smallest to largest
(defun merge-lists (x y)
	(declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
	(cond ((atom x) y)
		((atom y) x)
			((< (car x) (car y))
	 			(cons (car x) (merge-lists (cdr x) y)))
		(t (cons (car y) (merge-lists x (cdr y))))))

	;uses split to split into lists smaller than length x
(defthm split-size-x
  (implies (and (consp x) (consp (cdr x)))
           (and (< (acl2-count (car (split x)))
                   (acl2-count x))
                (< (acl2-count (mv-nth 1 (split x)))
                   (acl2-count x)))))

	;definition from textbook
(defun mergesort (x)
	(cond ((atom x) nil)
		((atom (cdr x)) x)
			(t (mv-let (a b)
		(split x)
			(merge-lists (mergesort a) (mergesort b))))))

	;checks if a list is in order, smallest to largest
(defun check-in-order (x)
  (cond ((atom (cdr x)) t)
	(t (and (<= (car x) (cadr x))
		(orderedp (cdr x))))))

	;(thm (orderedp (mergesort lst)))
(defthm orderedp-mergesort
  (orderedp (mergesort lst)))

; --------------- 11.16 ---------------

	;if y is not an empty list and car y is in list x, perm of appending y to the result of deleting car y from x
	;is equal to the perm of list x by appending the rest of y after car y is removed 
(defthm list-changes
	(implies (and (consp y)
     	(in (car y) x))
          	(perm (append (del (car y) x) y)
               	(append x (cdr y)))))

(defthm merge-lists-append
	(perm (merge-lists x y)
     	(append x y))
   
	:hints (("Goal" :induct (merge-lists x y))))

	;(append x (cons a y)) and (cons a (append x y)) are the same thing
(defthm perm-cons
	(perm (append x (cons a y)) (cons a (append x y))))

	;combines the split lists in order, critical to make mergesort work
(defthm perm-append-split-lists
	(perm (append (car (split lst)) (mv-nth 1 (split lst))) lst))

(defthm perm-mergesort
	(perm (mergesort lst) lst))

