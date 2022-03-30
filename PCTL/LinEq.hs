module LinEq (solveSystem, toEchelonForm, backSubstitution,
              validateMatrix, identityMatrix) where


type Matrix = (Int, Int, [[Double]])


-- Resuelve el sistema de ecuaciones lineales representado por la
-- matriz aumentada mat
-- Devuelve un vector con las soluciones del sistema
solveSystem :: Matrix -> [Double]
solveSystem mat = backSubstitution $ toEchelonForm mat


-- Valida que la matriz a sea de tamaño m x n
validateMatrix :: Matrix -> Bool
validateMatrix ( m, n, a )
    = width && height
    where size [] = 0
          size (x:xs) = 1 + size xs
          width = and $ map (\x->(size x)==n) a
          height = (size a) == m

-- Genera una matriz indentidad de n x n
identityMatrix :: Int -> Matrix
identityMatrix n = (n, n, mat)
    where mat = map row [1..n]
          row i = (ceros (i-1)) ++ [1.0] ++ (ceros (n-i))
          ceros n = take n $ repeat 0.0


-- Transforma una matriz a forma echelon con el triangulo inferior izq
-- en ceros
toEchelonForm :: Matrix -> Matrix
toEchelonForm (m,n,a) = reduced_a
    where reduced_a = toEch 1 (m,n,a)


-- Transforma una matriz a forma echelon paso a paso especificando
-- el pivote
toEch :: Int -> Matrix -> Matrix
toEch pivot (m,n,a)
    = if pivot==m
      then (m,n,a)
      else toEch (pivot+1) $ (m,n,r1)
    where r1 = (toPivot pivot r) ++ (reduceNext pivot p_row r2)
          r = getA $ sortByAbs pivot (m,n,a)
          r2 = (fromPivot pivot r)
          getA (m,n,a) = a
          p_row = pivotRow pivot r
          fromPivot p (x:xs) = if p==1 then xs else fromPivot (p-1) xs
          toPivot p (x:xs) = if p==1 then [x] else x:(toPivot (p-1) xs)
          pivotRow p mat = mat!!(p-1)

-- Elimina la variable pivote de la matriz (x:xs)
reduceNext _ _ [] = []
reduceNext pivot p_row (x:xs)
    = sum : (reduceNext pivot p_row xs)
    where c1 = p_row!!(pivot-1)
          c2 = x!!(pivot-1)
          c = -c2/c1
          mult1 c (x:xs) = (c*x):(mult1 c xs)
          mult1 _ [] = []
          mult = mult1 c p_row
          sum1 (x:xs) (y:ys) = (x+y):(sum1 xs ys)
          sum1 [] _ = []
          sum = sum1 mult x


-- ordena desendentemete por valor absoluto la columna pivote
sortByAbs :: Int -> Matrix -> Matrix
sortByAbs pivot (m,n,a)
    = if pivot==m then (m,n,a) else sort4 sort3
    where sort1 p (x:xs) =
              if xs == []
              then x:[]
              else if nextGt p (x:xs)
                   then (head xs) : (sort1 (p+1) (x:(tail xs)))
                   else x : (sort1 (p+1) xs)
          sort2 rep p (m,n,a) =
              if rep == 0
              then (m,n,a)
              else sort2 (rep-1) p (m,n,(sort1 p a))
          sort3 = sort2 (m-pivot) pivot (m,n,(fromPivot pivot a))
          sort4 (m,n,b) = (m,n,((toPivot pivot a)++b))
          nextGt p (x:xs) = (abs (x!!(p-1))) < (abs ((head xs)!!(p-1)))
          fromPivot p (x:xs) = if p==1 then (x:xs) else fromPivot (p-1) xs
          toPivot p (x:xs) = if p==1 then [] else x:(toPivot (p-1) xs)


-- hace backsubstitution a una matriz que ya está en forma echelon
-- devuelve un vector de soluciones
backSubstitution :: Matrix -> [Double]
backSubstitution (m,n,a) = back 1 m a --(toNZ (m+1))

-- hace backsubstitution de la ecuación i-ésima hasta la 1
-- la matriz l debe tener n ecuaciones
-- devuelve un vector de soluciones
back :: Int -> Int -> [[Double]] -> [Double]
back i n l
    = if i == n
      then let rown = head l
               xn = (rown!!n) / (rown!!(n-1))
           in [xn]
      else let s1 = back (i+1) n (tail l)
               len1 = length s1
               s2 = (toNZ (n-len1)) ++ s1
               r = head l
               b_ax = substituteRow r s2
               ai = r!!(i-1)
               xi = b_ax / ai
           in xi:s1
    where substituteRow row sol_vec
              = let r_row = reverse row
                    b = head r_row
                    r_sol = reverse sol_vec
                    mult = prod (tail r_row) r_sol
                    ax = sum mult
                    prod (x:xs) (y:ys) = (x*y) : (prod xs ys)
                    prod [] _ = []
                in  b - ax
          toNZ n = take n $ repeat 0.0
          fromN n l = if n==1 then l else fromN (n-1) (tail l)

--          toNZ     0 = []
--          toNZ (n+1) = 0.0 : (toNZ n)

-- ejemplos de matrices
mat1 = (3::Int,4::Int,[[2.0,   6.0,  10.0,   0.0],
                       [1.0,   3.0,   3.0,   2.0],
                       [3.0,  14.0,  28.0,  -8.0]])

mat2 = (2::Int,3::Int,[[0.001,  1.0,  3],
                       [  1.0,  2.0,  5]])

mat3 = (3::Int,4::Int,[[30.0,        -20.0,        -10.0,    0.0],
                       [ 0.0,  (125.0/3.0),  -(50.0/3.0),    0.0],
                       [ 0.0,          0.0,         40.0,  200.0]])

mat4 = (3::Int,4::Int,[[ 30.0,  -20.0,  -10.0,    0.0],
                       [-20.0,   55.0,  -10.0,    0.0],
                       [-10.0,  -10.0,   50.0,  200.0]])
