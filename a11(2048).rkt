;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname a11) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f ())))
(define handin "a11")
(define collaboration-statement "I worked alone")
(require 2htdp/image)
(require 2htdp/universe)

;;;;; FROM a10

;;;;;;;;;;;;;;;;
;;; problem 2
;;;;;;;;;;;;;;;;

; list/head : Nat [ListOf X] -> [ListOf X]
; (list/head n alist) returns the first n elements of the given list

(check-satisfied (list/head 2 '(a b c)) cons?)
(check-expect (list/head 2 '(a b c)) (list 'a 'b))

(define (list/head init-n init-alist)
  (local
    [(define (help n alist)
       (cond
         [(= n 0) '()]
         [(empty? alist) 
           (error 'list/head (format "~s is too large for ~s"
                                     init-n init-alist))]
         [else (cons (first alist) (help (sub1 n) (rest alist)))]))]
    (help init-n init-alist)))

(check-error (list/head 5 '(a b c))
             "list/head: 5 is too large for (a b c)")
          
; list/tail : Nat [ListOf X] -> [ListOf X]
; (list/tail n alist) returns everything but the first n elements

(check-satisfied (list/tail 2 '(a b c)) cons?)
(check-expect (list/tail 2 '(a b c)) (list 'c))

(define (list/tail init-n init-alist)
  (local
    [(define (help n alist)
       (cond
         [(= n 0) alist]
         [(empty? alist)
          (error 'list/tail (format "~s is too large for ~s"
                                    init-n init-alist))]
         [else (help (sub1 n) (rest alist))]))]
    (help init-n init-alist)))

(check-error (list/tail 5 '(a b c))
             "list/tail: 5 is too large for (a b c)")

;;;;;;;;;;;;;;;;
;;; problem 3
;;;;;;;;;;;;;;;;

; flatten : [ListOf List] -> [ListOf X]
; (flatten alist) returns the result of appending all sublists
; together into one list

(check-satisfied (flatten '((a b) (c) (d e f g) (h i j))) cons?)
(check-expect (flatten '((a b) (c) (d e f g) (h i j)))
              (list 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j))

(define (flatten alist)
  (cond
    [(empty? alist) empty]
    [else (foldr append '() alist)]))

(check-expect (flatten '()) empty)

;;;;;;;;;;;;;;;
;;; problem 4
;;;;;;;;;;;;;;;

; pop-up : PosInt [ListOf X] -> [ListOf lists]
; (pop-up n ls) returns the the result of grouping elements by length n
; in ls into sublists.


(check-satisfied (pop-up 2 '(a b c d e f g h)) cons?)
(check-expect (pop-up 2 '(a b c d e f g h))
             (list (list 'a 'b) (list 'c 'd) (list 'e 'f) (list 'g 'h)))

(define (pop-up n ls)
  (cond
    [(empty? ls) '()]
    [else (cons (list/head n ls) (pop-up  n (list/tail n ls)))]))

(check-expect (pop-up 3 '(a b c d e f))
              (list (list 'a 'b 'c) (list 'd 'e 'f)))

;;;;; 5c
(define (iterate/no-invarient f n x)
  (local
    [(define (help n)
       (cond
         [(zero? n) x]
         [else (f (help (sub1 n))) ]))]
    (help n)))

(check-expect (iterate/no-invarient add1 3 4) 7)
(check-expect (iterate/no-invarient sub1 3 4) 1)
(check-expect 
 (iterate/no-invarient rest 4 '(a b c d e f g)) (list 'e 'f 'g))

;;;;;;;;;;;;;;;
;;; problem 6
;;;;;;;;;;;;;;;

; overwrite : [ListOf X] Nat Any -> [ListOf X]
; (overwrite ls i value) returns the list resulting from replacing the
; element at index i in ls with the given value

(check-satisfied (overwrite '(a) 0 'b) cons?)
(check-expect (overwrite '(a) 0 'b) (list 'b))

(define (overwrite init-ls init-i value)
  (local
    [(define (help ls i)
       (cond
         [(empty? ls) 
          (error 'overwrite (format "~s is too large for ~s"
                                    init-i init-ls))]
         [(equal? i 0) (cons value (rest ls))]
         [else (cons (first ls) (help (rest ls) (sub1 i)))]))]
    (help init-ls init-i)))

(check-expect (overwrite '(x x x - x x x x) 3 'x) 
              (list 'x 'x 'x 'x 'x 'x 'x 'x))

;;;;;;;;;;;;;;;
;;; problem 7
;;;;;;;;;;;;;;;

;;;;;;;;;;;;;
;; The Model
;;;;;;;;;;;;;

;;;;; 7a

#|
A TileValue is either:
- '-
- 0 <= TileValue <= 12
|#

;;; i

(define blank '-)

;;; ii

; blank? : X -> Bool
; (blank? item) returns true iff x corresponds to the blank tile

(check-satisfied (blank? blank?) boolean?)
(check-expect (blank? blank?) false)

(define (blank? item)
  (if (equal? item blank)
      true
      false))

(check-expect (blank? blank) true)
(check-expect (blank? 2048) false)

;;;;; 7b

#| 
A Board is either:
- (cons TileValue)
- (cons [ListOf TileValue] TileValue)
|#

(define b1 (list (list 64 32) (list 16 16)))

(define b2 (list
 (list 2 2 2 2)
 (list 4 '- 4 '-)
 (list '- 8 8 8)
 (list 16 '- '- 16)))

(define b3 (list
 (list 16 64 8 256 4)
 (list 1024 1024 1024 32 128)
 (list 64 32 128 '- '-)
 (list 4 4 32 '- '-)
 (list 2 '- '- 512 '-)))

;;;;; 7c

; board-full? : Board -> Bool
; (board-full? board) returns true iff the board has no blank tiles

(check-satisfied (board-full? b2) boolean?)
(check-expect (board-full? b2) false)

(define (board-full? board)
  (if (empty? (filter blank? (flatten board)))
      true
      false))

(check-expect (board-full? '((4))) true)
(check-expect (board-full? b1) true)

;;;;; 7d

; add-new-tile : Board -> Board
; (add-new-tile board) returns a board with one of the blank spaces of
; the previouse board replaced by a new tile of value 2 or 4

(check-expect (add-new-tile '((4))) (list (list 4)))
(check-expect (add-new-tile b1) (list (list 64 32) (list 16 16)))

(define (add-new-tile board)
  (local
    [(define rows (length board))
     (define helper
       (if (> 8 (random 10))
           2
           4))
     (define cols (length (first board)))
     (define num_tiles (* rows cols))
     (define tiles (flatten board))
     (define blanklist (lambda (ls i blanks)
                         (cond
                           [(empty? ls) blanks]
                           [(blank? (first ls)) (blanklist (rest ls)
                                             (add1 i) (cons i blanks))]
                           [else (blanklist (rest ls) 
                                            (add1 i) blanks)])))
     (define blanks (blanklist tiles 0 empty))
     ; add : Num -> [ListOf Tiles]
     (define add (lambda (n) (overwrite tiles n helper)))]
                                 
    (cond
      [(empty? board) '()]
      [(board-full? board) board]
      [else (pop-up rows (add  (list-ref blanks 
                                    (random (length blanks)) ))  )])))  


;;;;; 7e

; make-board : PosInt Nat -> Board
; (make-board n m) returns a nXn board with m non-blank tiles

(check-expect (make-board 1 0) (list (list '-)))


(define (make-board n m)
  (iterate/no-invarient add-new-tile m (make-list n 
                                                  (make-list n blank))))

;;;;; 7f

; board-square? : Board -> Bool
; (board-square? board) returns true iff the board is of demensions nXn
; for some positive integer n

(check-expect (board-square? '()) false)
(check-expect (board-square? b3) true)

(define (board-square? board)
  (local
    [(define rows (length board))
     (define (help x y)
       (and (= rows (length x)) y))]
    (if (zero? rows) false
        (foldr help true board))))

(check-expect (board-square? '((2 4) (8 16 32))) false)
(check-expect (board-square? '((2 2 2 2) (4 4 4 4) (2 2 2) (4 4 4 4)))
              false)

;;;;; 7g

; game-won? : Board -> Bool
; (game-won? board) returns true iff the board contains a 2048 tile

(check-satisfied (game-won? b3) boolean?)
(check-expect (game-won? b3) false)

(define (game-won? board)
  (member? 2048 (flatten board)))
               

(check-expect (game-won? '((2 2 2) (2 2048 2) (- - -))) true)


;;;;;;;;;;;;;;;
;;; problem 8
;;;;;;;;;;;;;;;

;;;;;;;;;;;;;
;; The View
;;;;;;;;;;;;;

;;;;; 8a

(define TILE-SIZE 60)
(define FONT-SIZE 30)
(define GRID-SPACING 3)
(define GRID-COLOR (make-color 187 173 160))

;;;;; 8b

; *********** provided code *********** (do not remove this comment)
; tile->image : TileValue PosInt Color Color -> Image
; (tile->image tile-val font-size foreground-color background-color) 
; returns the image corresponding to a tile with the given properties

(define (tile->image tile-val font-size 
                     foreground-color background-color)
  (local
   [(define back-image (overlay 
                        (square TILE-SIZE 'solid background-color)
                        (square (+ TILE-SIZE (* 2 GRID-SPACING))
                                'solid GRID-COLOR)))]
   (if (blank? tile-val)
       back-image
       (overlay 
        (text (number->string tile-val) font-size foreground-color)
        back-image))))

;;;;; 8c

;; background-color : TileValue -> Color
;; (background-color tilevalue) returns background
;; color of the tile.
(define (background-color tilevalue)
  (cond
    [(equal? tilevalue blank) (make-color 204 192 179)]
    [(equal? tilevalue 2) (make-color 238 228 218)]
    [(equal? tilevalue 4) (make-color 237 224 200)]
    [(equal? tilevalue 8) (make-color 242 177 121)]
    [(equal? tilevalue 16) (make-color 245 149 99)]
    [(equal? tilevalue 32) (make-color 246 124 95)]
    [(equal? tilevalue 64) (make-color 246 94 59)]
    [(equal? tilevalue 128) (make-color 237 207 114)]
    [(equal? tilevalue 256) (make-color 237 204 97)]
    [(equal? tilevalue 512) (make-color 237 200 80)]
    [(equal? tilevalue 1024) (make-color 237 197 63)]
    [(equal? tilevalue 2048) (make-color 237 194 46)]
    [else false]))

;; foreground-color : TileValue -> Color
;; (foreground-color tilevalue) returns the foreground
;; color of the tile.
(define (foreground-color tilevalue)
  (if 
   (or (blank? tilevalue) (>= tilevalue 4)) 
   (make-color 255 255 255) 
   (make-color 105 105 105)))


; val->image : TileValue -> Image
; (val->image tilevalue) returns the image associated with value given.

(define (val->image tilevalue)
  (cond
    [(member? tilevalue 
             (list blank 2 4 8 16 32 64)) 
     (tile->image tilevalue FONT-SIZE 
               (foreground-color tilevalue) 
               (background-color tilevalue))]
    [(member? tilevalue 
             (list 128 256 512)) 
     (tile->image tilevalue (- FONT-SIZE 4)
               (foreground-color tilevalue) 
               (background-color tilevalue))]
    [(member? tilevalue 
             (list 1024 2048)) 
     (tile->image tilevalue (- FONT-SIZE 6) 
               (foreground-color tilevalue) 
               (background-color tilevalue))]
    [else (error 'val->image
                 (format "unknown tile value ~s"
                         tilevalue))]))
    

;;;;; 8d

;; row-builder : [ListOf TileValue] -> Image
;; (row-builder row) returns an image of
;; one row of the board.
(define (row-builder row)
  (foldr (lambda (x y) (beside (val->image x) y)) empty-image row))


; board->image : Board -> Image
; (board->image board) returns the image associated with the given board
; list
(define (board->image board)
  (foldr 
   (lambda (x y) 
     (above (row-builder x) y)) 
   empty-image board))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [a11]


;;;;;;;;;;;;;;;;
;;; problem 1
;;;;;;;;;;;;;;;;

; invert/v1 : [ListOf X] -> [ListOf X]
; (invert/v1 ls) returns the result of reversing the top-level
; elements of ls
(define (invert/v1 ls)
  (local [; help : [ListOf X] [ListOf X] -> [ListOf X]
          (define (help ls acc)
            (cond
             [(empty? ls) acc]
             [else (help (rest ls) (cons (first ls) acc))]))]
  (help ls '())))
 
;; invert/v2 : [ListOf X] -> [ListOf X]
;; (invert/v2 ls) returns the result of reversing the top-level
;; elements of ls
;(define (invert/v2 ls)
;  (cond
;   [(empty? ls) '()]
;   [else (append (invert/v2 (rest ls)) (list (first ls)))]))

;;;;; 1a

; '(a b c d e)
; '(a) '(b c d e)
; '(a b) '(c d e)
; '(a b c) '(d e)
; '(a b c d) '(e)
; '(a b c d e)

;;;;; 1b
; '(a b c d e)
; '(a '(b c d e))
; '(a '(b '(c d e)))
; '(a '(b '(c '(d e))))
; '(a '(b '(c '(d '(e)))))
; '(a '(b '(c '(d e))))
; '(a '(b '(c d e)))
; '(a '(b c d e))
; '(a b c d e)

;;;;; 1c
; The help function in v1 is tail-recurisive because the previous number
; or the previous answer is rembered in an accumulator and the 
; accumulator changes as you go across the board insted of changing
; after passing through the board twice

;;;;; 1d
; v2 is Not tail recursive because the board is passed over two 
; times so the recursion can take place. the recursion is also 
; not instant which further more makes this function non-tail recursive


;;;;; 1e

#|
 
       n       invert/v1     invert/v2     reverse
  -------------------------------------------------
      100        1              1
     1000         1             31
    10000        12              820
   100000       110             145500
 
|#

;;;;; 1f

; I think v2 is taking a longer time because it doesn't store the 
; previouse value rather it runs throug the code twice. I also
; think v2 is taking longer because it is not tail recursive and
; runs through a large list

;;;;; 1g
; I predict you will have to wait 4 hour to get the amount of time it
; would take for v2 to go thorugh a list of 1 million things

;;;;; 1h

;;;;;;;;;;;;;;;;
;;; problem 2
;;;;;;;;;;;;;;;;

;;;;; 2a

(check-expect (slide-row-left '()) empty)
(check-expect (slide-row-left '(-)) (list '-))
(check-expect (slide-row-left '(2)) (list 2))
(check-expect (slide-row-left '(- -)) (list '- '-))
(check-expect (slide-row-left '(2 -)) (list 2 '-))
(check-expect (slide-row-left '(- 2)) (list 2 '-))
(check-expect (slide-row-left '(2 2)) (list 4 '-))
(check-expect (slide-row-left '(2 4)) (list 2 4))
(check-expect (slide-row-left '(4 4)) (list 8 '-))
(check-expect (slide-row-left '(- - -)) (list '- '- '-))
(check-expect (slide-row-left '(2 - -)) (list 2 '- '-))
(check-expect (slide-row-left '(- 2 -)) (list 2 '- '-))
(check-expect (slide-row-left '(- - 2)) (list 2 '- '-))
(check-expect (slide-row-left '(2 2 -)) (list 4 '- '-))
(check-expect (slide-row-left '(2 - 2)) (list 4 '- '-))
(check-expect (slide-row-left '(- 2 2)) (list 4 '- '-))
(check-expect (slide-row-left '(2 4 -)) (list 2 4 '-))
(check-expect (slide-row-left '(2 - 4)) (list 2 4 '-))
(check-expect (slide-row-left '(- 2 4)) (list 2 4 '-))
(check-expect (slide-row-left '(2 2 2)) (list 4 2 '-))
(check-expect (slide-row-left '(4 2 2)) (list 4 4 '-))
(check-expect (slide-row-left '(2 4 2)) (list 2 4 2))
(check-expect (slide-row-left '(2 2 4)) (list 4 4 '-))
(check-expect (slide-row-left '(2 4 8)) (list 2 4 8))
(check-expect (slide-row-left '(2 4 8 16)) (list 2 4 8 16))
(check-expect (slide-row-left '(2 4 8 -)) (list 2 4 8 '-))
(check-expect (slide-row-left '(4 4 8 8)) (list 8 16 '- '-))
(check-expect (slide-row-left '(- - - -)) (list '- '- '- '-))
(check-expect (slide-row-left '(2 - - -)) (list 2 '- '- '-))
(check-expect (slide-row-left '(- 2 - -)) (list 2 '- '- '-))
(check-expect (slide-row-left '(- - 2 -)) (list 2 '- '- '-))
(check-expect (slide-row-left '(- - - 2)) (list 2 '- '- '-))
(check-expect (slide-row-left '(2 2 - -)) (list 4 '- '- '-))
(check-expect (slide-row-left '(2 - 2 -)) (list 4 '- '- '-))
(check-expect (slide-row-left '(2 - - 2)) (list 4 '- '- '-))
(check-expect (slide-row-left '(- 2 - 2)) (list 4 '- '- '-))
(check-expect (slide-row-left '(- 2 2 -)) (list 4 '- '- '-))
(check-expect (slide-row-left '(- - 2 2)) (list 4 '- '- '-))
(check-expect (slide-row-left '(2 4 - -)) (list 2 4 '- '-))
(check-expect (slide-row-left '(- 2 4 -)) (list 2 4 '- '-))
(check-expect (slide-row-left '(- - 2 4)) (list 2 4 '- '-))
(check-expect (slide-row-left '(2 - 4 -)) (list 2 4 '- '-))
(check-expect (slide-row-left '(- 2 - 4)) (list 2 4 '- '-))
(check-expect (slide-row-left '(2 - - 4)) (list 2 4 '- '-))
(check-expect (slide-row-left '(2 2 2 -)) (list 4 2 '- '-))
(check-expect (slide-row-left '(- 2 2 2)) (list 4 2 '- '-))
(check-expect (slide-row-left '(2 2 2 2)) (list 4 4 '- '-))
(check-expect (slide-row-left '(4 2 2 -)) (list 4 4 '- '-))
(check-expect (slide-row-left '(2 4 2 -)) (list 2 4 2 '-))
(check-expect (slide-row-left '(2 2 4 -)) (list 4 4 '- '-))
(check-expect (slide-row-left '(- 4 2 2)) (list 4 4 '- '-))
(check-expect (slide-row-left '(- 2 4 2)) (list 2 4 2 '-))
(check-expect (slide-row-left '(- 2 2 4)) (list 4 4 '- '-))
(check-expect (slide-row-left '(4 2 2 2)) (list 4 4 2 '-))
(check-expect (slide-row-left '(2 4 2 2)) (list 2 4 4 '-))
(check-expect (slide-row-left '(2 2 4 2)) (list 4 4 2 '-))
(check-expect (slide-row-left '(2 2 2 4)) (list 4 2 4 '-))
(check-expect (slide-row-left '(2 2 2 2 2 2 2 2)) 
              (list 4 4 4 4 '- '- '- '-))
(check-expect (slide-row-left '(2 2 2 2 2 2 2 2 2 2)) 
              (list 4 4 4 4 4 '- '- '- '- '-))
(check-expect (slide-row-left '(- - 2 2 - 4)) (list 4 4 '- '- '- '-))
              

;;;;; 2b

; slide-row-left : [ListOf Tiles] -> [ListOf Tiles] 
; (slide-row-left row) returns a list with each value
; moved over one and added together iff the valuse are equal

(define (slide-row-left row)
  (local
    [(define (help a-row last-num blanks)
       (cond
         [(and (empty? a-row) (not (false? last-num)))
          (cons last-num blanks)]
         [(empty? a-row) blanks]
         [(blank? (first a-row)) 
          (help (rest a-row) last-num (cons (first a-row) blanks))]
         [(false? last-num) 
          (help (rest a-row) (first a-row) blanks)]
         [(equal? (first a-row) last-num) 
          (cons (+ last-num (first a-row)) 
                (help (rest a-row) false (cons blank blanks)))] 
         [(not (equal? (first a-row) last-num))
          (cons last-num (help (rest a-row) (first a-row) blanks))]))]
    (help row false '())))



;;;;;;;;;;;;;;;;
;;; problem 3
;;;;;;;;;;;;;;;;

; slide-row-right : [ListOf Tiles] -> [ListOf Tiles]
; (slide-row-right row ) returns a 

(check-expect (slide-row-right '(- - 2 2 - 2 4 - - 4)) 
              (list '- '- '- '- '- '- '- 2 4 8))
(check-expect (slide-row-right '(- - 8 - 4)) 
              (list '- '- '- 8 4))

(define (slide-row-right row)
   (reverse (slide-row-left (reverse row))))

(check-expect (slide-row-right '(- 16 - 2048 -))
              (list '- '- '- 16 2048))

;;;;;;;;;;;;;;;;
;;; problem 4
;;;;;;;;;;;;;;;;

; slide-left : Board -> Board
; (slide-left board) returns the board after sliding all rows to the
; left
(define (slide-left board)
     (map slide-row-left board))
     
     
; slide-right : Board -> Board
; (slide-right board) returns the board after sliding all rows to the
; right
(define (slide-right board)
  (map slide-row-right board))

;;;;;;;;;;;;;;;;
;;; problem 5
;;;;;;;;;;;;;;;;

; transpose : [ListOf List] -> [ListOf List] or Bool
; (transpose lls)  returns the result of reflecting the elements along
; the main diagonal
(define (transpose lls)
  (cond 
    [(empty? (first lls)) empty]
    [else (cons (map first lls) (transpose (map rest lls)))]))



;;;;;;;;;;;;;;;;
;;; problem 6
;;;;;;;;;;;;;;;;

; slide-up : Board -> Board
; (slide-up board) returns the board after sliding all rows up
(define (slide-up board)
  (transpose (slide-left (transpose board))))



; slide-down : Board -> Board
; (slide-down board) returns the board after sliding all rows down
(define (slide-down board)
  (transpose (slide-right (transpose board))))

;;;;;;;;;;;;;;;;
;;; problem 7
;;;;;;;;;;;;;;;;

;;;;; 7a

; game-lost? : Board -> Bool
; (game-lost? ls) returns true iff the board represents a losing
; configuration

(define (game-lost? ls)
  (if (and (equal? (slide-right ls) ls)
           (equal? (slide-left ls) ls)
           (equal? (slide-up ls) ls)
           (equal? (slide-down ls) ls))
      true
      false))
;;;;; 7b

; game-over? : Board -> Bool
; (game-over? ls)  returns true iff ls represents either a winning or
; losing configuration

(define (game-over? ls)
  (if (or (game-lost? ls) (game-won? ls))
      true
      false))

;;;;;;;;;;;;;;;;
;;; problem 8
;;;;;;;;;;;;;;;;

; key-handler : Board String -> Board
; (key-handler board keystroke) If the key is anything other than an
; arrow key, the board is returned unchanged. Otherwise, the board is
; shifted in the indicated direction and we attempt to add a new tile
; to the board.

(define (key-handler init-board keystroke)
  (local
    [(define (helper board)
       (cond
         [(equal? keystroke "up") (slide-up board)]
         [(equal? keystroke "down") (slide-down board)]
         [(equal? keystroke "left") (slide-left board)]
         [(equal? keystroke "right") (slide-right board)]
         [else board]))
     (define new-board (helper init-board))]
        (if (not (equal? new-board init-board))
            (add-new-tile new-board)
            new-board)))


;;;;;;;;;;;;;;;;
;;; problem 9
;;;;;;;;;;;;;;;;

; main : PosInt -> Img
; (main n) returns the fully functinol game 2048
(define (main n)
  (local
    [(define board (make-board n 2))]
  (big-bang board
            [to-draw board->image]
            [on-key key-handler]
            [on-tick (lambda (board) board)]
            [stop-when game-over?])))