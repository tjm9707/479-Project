(in-package "ACL2")

(include-book "textbook/chap11/perm-append" :dir :system)


; 11.8
(defun less (x LST)
  	(cond ((atom LST) nil)
	((< (car LST) x)
	 (cons (car LST) (less x (cdr LST))))
	(t (less x (cdr LST)))))

; 11.9
(defun notless (x LST)
  	(cond ((endp LST) nil)
      ((< (car LST) x)
       (notless x (cdr LST)))
      (t (cons (car LST) (notless x (cdr LST))))))

; 11.10
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

; 11.11
 (defun lessp (x lst)
   (if (endp lst)
       t
     (and (< (car lst) x)
          (lessp x (cdr lst)))))
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
