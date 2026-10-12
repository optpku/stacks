/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Exact
import StacksCheckRecall

@[expose] public section

/-!
# Exactness for a finite principal-open cover

@stack 00EJ

Lemma 10.24.2 is the ring specialization of the principal-open Cech exactness API.
-/

universe u

variable {R : Type u} [CommRing R]
variable {n : ℕ}

/- Lemma 10.24.2 (1): the map `R → ∏ i, R_(f_i)` is injective when the `f_i`
generate the unit ideal. -/
@[stacks 00EJ "(1), injectivity"]
#check LocalizedModule.Away.Cech.familyMap_injective
  (R := R) (ι := Fin n) R

/- Lemma 10.24.2 (2): the image of `R → ∏ i, R_(f_i)` is the kernel of the
pairwise-difference map to `∏ i j, R_(f_i f_j)`. -/
@[stacks 00EJ "(2), exactness at the middle term"]
#check LocalizedModule.Away.Cech.familyMap_exact
  (R := R) (ι := Fin n) R
