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
              (equal (perm (del a y) x)
                     (perm y (cons a x))))
  
 ; The only way I could get this to work is with a hint
     :hints (("Goal" :induct (perm y x)))))

; Prove (implies (and (perm x y) (perm y z)) (perm x z))

(defthm perm-symmetric
    (implies (perm x y) (perm y x)))))

(local (defthm in-del-implies
         (implies (in x (del a y))
                  (in x y))))

(local (defthm perm-in-same
(IMPLIES (AND (NOT (IN X1 Z))
              (IN X1 Y))
         (NOT (PERM Y Z)))))

(local (defthm del-del
         (equal (del a (del b x))
                (del b (del a x)))))

(local (defthm in-del
         (implies (not (equal a b))
                  (equal (in a (del b y))
                         (in a y)))))

(local (defthm perm-del-del
         (implies (and (in a y)
                       (in a z))
                  (equal (perm y z)
                         (perm (del a y) (del a z))))))

(local (defthm perm-transitive
         (implies (and (perm x y) (perm y z)) (perm x z))))

(defequiv perm)
