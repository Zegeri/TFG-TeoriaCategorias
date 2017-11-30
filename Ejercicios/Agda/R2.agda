{-
   Copyright (c) 2017 Diego Pedraza.

   This is Free/Libre Open Source Software, released under the MIT License.
   For the full copyright and license information, please view the LICENSE
   file that was distributed with this source code.
 -}

module R2 where

open import Data.List using (List; _∷_; _++_; [_]; [])
open import Data.Nat
open import Data.Bool

record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

{- --------------------------------------------------------------- 
  Ejercicio 1.1. Definir la función
     sumaImpares :: nat ⇒ nat
  tal que (sumaImpares n) es la suma de los n primeros números
  impares. Por ejemplo,
     sumaImpares 5  =  25
  ---------------------------------------------------------------- -}

sumaImpares : ℕ → ℕ
sumaImpares 0 = 0
sumaImpares (suc n) = (2 * n + 1) + sumaImpares n

{- --------------------------------------------------------------- 
  Ejercicio 1.2. Demostrar que 
     sumaImpares n = n*n
  ----------------------------------------------------------------- -}
_≡_ : ℕ → ℕ → Bool
0 ≡ 0 = true
(suc n) ≡ (suc m) = n ≡ m
n ≡ 0 = false
0 ≡ m = false

lemaSumaImpares : {n : ℕ} → (sumaImpares n) ≡ (n * n)
lemaSumaImpares {zero} = ?
lemaSumaImpares {suc n} = ?

{-

{- --------------------------------------------------------------- 
  Ejercicio 2.1. Definir la función
     sumaPotenciasDeDosMasUno :: nat ⇒ nat
  tal que 
     (sumaPotenciasDeDosMasUno n) = 1 + 2^0 + 2^1 + 2^2 + ... + 2^n. 
  Por ejemplo, 
     sumaPotenciasDeDosMasUno 3  =  16
  ---------------------------------------------------------------- -}
 
fun sumaPotenciasDeDosMasUno :: "nat ⇒ nat" where
  "sumaPotenciasDeDosMasUno n = undefined"
 
{- --------------------------------------------------------------- 
  Ejercicio 2.2. Demostrar que 
     sumaPotenciasDeDosMasUno n = 2^(n+1)
  ----------------------------------------------------------------- -}
 
lemma "sumaPotenciasDeDosMasUno n = 2^(n+1)"
  oops
 
{- --------------------------------------------------------------- 
  Ejercicio 3.1. Definir la función
     copia :: nat ⇒ 'a ⇒ 'a list
  tal que (copia n x) es la lista formado por n copias del elemento
  x. Por ejemplo, 
     copia 3 x = [x,x,x]
  ---------------------------------------------------------------- -}
 
fun copia :: "nat ⇒ 'a ⇒ 'a list" where
  "copia n x = undefined"
 
{- --------------------------------------------------------------- 
  Ejercicio 3.2. Definir la función
     todos :: ('a ⇒ bool) ⇒ 'a list ⇒ bool
  tal que (todos p xs) se verifica si todos los elementos de xs cumplen
  la propiedad p. Por ejemplo,
     todos (λx. x>(1::nat)) [2,6,4] = True
     todos (λx. x>(2::nat)) [2,6,4] = False
  Nota: La conjunción se representa por ∧
  --------------------------------------------------------------- -}
 
fun todos :: "('a ⇒ bool) ⇒ 'a list ⇒ bool" where
  "todos p xs = undefined"
 
{- --------------------------------------------------------------- 
  Ejercicio 3.3. Demostrar que todos los elementos de (copia n x) son
  iguales a x. 
  ----------------------------------------------------------------- -}
 
lemma "todos (λy. y=x) (copia n x)"
  oops
 
{- --------------------------------------------------------------- 
  Ejercicio 4.1. Definir, recursivamente y sin usar (@), la función
     amplia :: 'a list ⇒ 'a ⇒ 'a list
  tal que (amplia xs y) es la lista obtenida añadiendo el elemento y al
  final de la lista xs. Por ejemplo,
     amplia [d,a] t = [d,a,t]
  ---------------------------------------------------------------- -}
 
fun amplia :: "'a list ⇒ 'a ⇒ 'a list" where
  "amplia xs y = undefined"
 
{- --------------------------------------------------------------- 
  Ejercicio 4.2. Demostrar que 
     amplia xs y = xs @ [y]
  ----------------------------------------------------------------- -}
 
lemma "amplia xs y = xs @ [y]"
  oops
-}
