; 11.5

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

(local (defthm perm-reflect
         (perm x x)))

(local
 (encapsulate ()

  (local (defthm perm-del
     (implies (in a y)
              (equal (perm y (cons a x))
                     (perm (del a y) x)))
            
  
 ; The only way I could get this to work is with a hint
     :hints (("Goal" :induct (perm y x)))))

; Prove (implies (and (perm x y) (perm y z)) (perm x z))

    ;x + y = y + x
(defthm perm-switch
    (implies (perm x y) (perm y x)))))
	
	; x - a + y = x + y
(local (defthm in-del
         (implies (in x (del a y))
                  (in x y))))

	;x1 + z !=  x1 + y
(local (defthm perm-in-same
(IMPLIES (AND (NOT (IN X1 Z))
              (IN X1 Y))
         (NOT (PERM Y Z)))))

(local (defthm del2
         (equal (del a (del b x))
                (del b (del a x)))))

(local (defthm in-del3
         (implies (not (equal a b))
                  (equal (in a (del b y))
                         (in a y)))))

(local (defthm perm-del2
         (implies (and (in a y)
                       (in a z))
                  (equal (perm y z)
                         (perm (del a y) (del a z))))))

(local (defthm perm-transitive
         (implies (and (perm x y) (perm y z)) (perm x z))))

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

; ---------------------------------------------------------------------------
; Exercise 11.6

#|
:trans1(defcong perm perm (append x y) 1)
(DEFTHM PERM-IMPLIES-PERM-APPEND-1
         (IMPLIES (PERM X X-EQUIV)
                  (PERM (APPEND X Y) (APPEND X-EQUIV Y)))
         :RULE-CLASSES (:CONGRUENCE))
|#

; ---------------------------------------------------------------------------
; Exercise 11.7

	; needs a lemma for in

	(defthm in-lemma
  		(equal (in a (append x y))
       	  (or (in a x) (in a y))))


	;needs another lemma for del

(defthm del-lemma
   (equal (del a (append x y))
         (if (in a x)
             (append (del a x) y)
           (append x (del a y)))))

(defcong perm perm (append x y) 1))
(defcong perm perm (append x y) 2))

; ---------------------------------------------------------------------------
; 11.8
(defun less (x lst)
  	(cond ((atom lst) nil)
	((< (car lst) x)
	 (cons (car lst) (less x (cdr lst))))
	(t (less x (cdr lst)))))
; ---------------------------------------------------------------------------

; 11.9
(defun notless (x lst)
  	(cond ((endp lst) nil)
      ((< (car lst) x)
       (notless x (cdr lst)))
      (t (cons (car lst) (notless x (cdr lst))))))

; ---------------------------------------------------------------------------
; 11.10
	
	;definition from textbook
 (defun qsort (x)
    (cond ((atom x) nil)
          (t (append (qsort (less (car x) (cdr x)))
                     (list (car x))
                     (qsort (notless (car x) (cdr x)))))))


 (defthm perm-append-cons-2
   (perm (append x (cons a y))
         (cons a (append x y))))

 (defthm perm-append-less-notless
   (perm (append (less x1 x2)
                 (cons x1 (notless x1 x2)))
         (cons x1 x2)))

 (defthm perm-qsort
   (perm (qsort x) x))

; ---------------------------------------------------------------------------
; 11.11
 (defun lessp (x lst)
   (if (endp lst)
       t
     (and (< (car lst) x)
          (lessp x (cdr lst)))))

; ---------------------------------------------------------------------------
; 11.12
 (defun notlessp (x lst)
   (if (endp lst)
       t
     (and (not (< (car lst) x))
          (notlessp x (cdr lst)))))

 (defun orderedp (lst)
   (if (or (endp lst) (endp (cdr lst)))
       t
     (and (<= (car lst) (cadr lst))
          (orderedp (cdr lst)))))

; ---------------------------------------------------------------------------
; 11.13
 (defthm orderedp-append
   (equal (orderedp (append x y))
          (if (consp x)
              (if (consp y)
                  (and (orderedp x)
                       (orderedp y)
                       (<= (car (last x)) (car y)))
                (orderedp x))
            (orderedp y))))
