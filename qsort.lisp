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
      (t (cons (car LST) (notless x (cdr lst))))))

; 11.10
 (defun qsort (x)
    (cond ((atom x) nil)
          (t (append (qsort (less (car x) (cdr x)))
                     (list (car x))
                     (qsort (notless (car x) (cdr x)))))))