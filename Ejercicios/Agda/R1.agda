{-
   Copyright (c) 2017 Diego Pedraza.

   This is Free/Libre Open Source Software, released under the MIT License.
   For the full copyright and license information, please view the LICENSE
   file that was distributed with this source code.
 -}

module R1 where

open import Data.List using (List; _∷_; _++_; [_]; [])
open import Data.Nat
open import Data.Bool

record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

{- ----------------------------------------------------------------
  Ejercicio 1. Definir, por recursión, la función
     longitud :: 'a list ⇒ nat
  tal que (longitud xs) es la longitud de la listas xs. Por ejemplo,
     longitud [a,b,c] = 3
  ----------------------------------------------------------------- -}

longitud : ∀ {A : Set} → List A → ℕ
longitud [] = 0
longitud (x ∷ xs) = 1 + longitud xs

{- ---------------------------------------------------------------
  Ejercicio 2. Definir la función
     fun intercambia :: 'a × 'b ⇒ 'b × 'a
  tal que (intercambia p) es el par obtenido intercambiando las
  componentes del par p. Por ejemplo,
     intercambia (u,v) = (v,u)
  ---------------------------------------------------------------- -}

intercambia : ∀ {A} {B : Set} → Pair A B → Pair B A
intercambia (a , b) = (b , a)

{- ---------------------------------------------------------------
  Ejercicio 3. Definir, por recursión, la función
     inversa :: 'a list ⇒ 'a list
  tal que (inversa xs) es la lista obtenida invirtiendo el orden de los
  elementos de xs. Por ejemplo,
     inversa [a,d,c] = [c,d,a]
  ---------------------------------------------------------------- -}

inversa : ∀ {A : Set} → List A → List A
inversa (x ∷ xs) = inversa (xs) ++ [ x ]
inversa [] = []

{- ---------------------------------------------------------------
  Ejercicio 4. Definir la función
     repite :: nat ⇒ 'a ⇒ 'a list
  tal que (repite n x) es la lista formada por n copias del elemento
  x. Por ejemplo,
     repite 3 a = [a,a,a]
  ---------------------------------------------------------------- -}

repite : ∀ {A : Set} → ℕ → A → List A
repite 0 x = []
repite (suc n) x = x ∷ repite n x

{- ---------------------------------------------------------------
  Ejercicio 5. Definir la función
     conc :: 'a list ⇒ 'a list ⇒ 'a list
  tal que (conc xs ys) es la concatención de las listas xs e ys. Por
  ejemplo,
     conc [a,d] [b,d,a,c] = [a,d,b,d,a,c]
  ---------------------------------------------------------------- -}

conc : ∀ {A : Set} → List A → List A → List A
conc [] ys = ys
conc (x ∷ xs) ys = x ∷ conc xs ys

{- ---------------------------------------------------------------
  Ejercicio 6. Definir la función
     coge :: nat ⇒ 'a list ⇒ 'a list
  tal que (coge n xs) es la lista de los n primeros elementos de xs. Por
  ejemplo,
     coge 2 [a,c,d,b,e] = [a,c]
  ---------------------------------------------------------------- -}

coge : ∀ {A : Set} -> ℕ → List A → List A
coge 0 xs = []
coge n [] = []
coge (suc n) (x ∷ xs) = x ∷ coge n xs

{- ---------------------------------------------------------------
  Ejercicio 7. Definir la función
     elimina :: nat ⇒ 'a list ⇒ 'a list
  tal que (elimina n xs) es la lista obtenida eliminando los n primeros
  elementos de xs. Por ejemplo,
     elimina 2 [a,c,d,b,e] = [d,b,e]
  ---------------------------------------------------------------- -}

elimina : ∀ {A : Set} → ℕ → List A → List A
elimina 0 xs = xs
elimina n [] = []
elimina (suc n) (x ∷ xs) = elimina n xs

{- --------------------------------------------------------------- 
  Ejercicio 8. Definir la función
     esVacia :: 'a list ⇒ bool
  tal que (esVacia xs) se verifica si xs es la lista vacía. Por ejemplo,
     esVacia [a] = False
  ---------------------------------------------------------------- -}

esVacia : ∀ {A : Set} → List A → Bool
esVacia [] = true
esVacia (x ∷ xs) = false

{- ---------------------------------------------------------------
  Ejercicio 9. Definir la función
     inversaAc :: 'a list ⇒ 'a list
  tal que (inversaAc xs) es a inversa de xs calculada usando
  acumuladores. Por ejemplo,
     inversaAc [a,c,b,e] = [e,b,c,a]
  ---------------------------------------------------------------- -}

inversaAcAux : ∀ {A : Set} → List A → List A → List A
inversaAcAux [] ys = ys
inversaAcAux (x ∷ xs) ys = inversaAcAux xs (x ∷ ys)

inversaAc : ∀ {A : Set} → List A → List A
inversaAc xs = inversaAcAux xs []

{- ---------------------------------------------------------------
  Ejercicio 10. Definir la función
     sum :: nat list ⇒ nat
  tal que (sum xs) es la suma de los elementos de xs. Por ejemplo,
     sum [3,2,5] = 10
  ---------------------------------------------------------------- -}

sum  : List ℕ → ℕ
sum [] = 0
sum (x ∷ xs) = x + sum xs

{- ---------------------------------------------------------------
  Ejercicio 11. Definir la función
     map :: ('a ⇒ 'b) ⇒ 'a list ⇒ 'b list
  tal que (map f xs) es la lista obtenida aplicando la función f a los
  elementos de xs. Por ejemplo,
     map (λx. 2*x) [3,2,5] = [6,4,10]
  ---------------------------------------------------------------- -}

map : ∀ {A B : Set} → (A → B) → List A → List B
map f (x ∷ xs) = f x ∷ (map f xs)
map f [] = []
