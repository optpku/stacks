/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.Principal
import StacksCheckRecall

/-!
# Lemma 15.91.1

The current adic-completion API gives the source statement for commutative
rings: every positive principal-power quotient agrees with the corresponding
quotient of the principal-adic completion.

@stack 0BNJ
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R] (f : R) (n : ℕ+)

/- Lemma 15.91.1 (0BNJ): the canonical map
`R / (f)^n ⟶ R^ / (f)^n R^` is bijective for every positive `n`. -/
@[stacks 0BNJ "principal-adic completion quotient comparison"]
#check (AdicCompletion.principalPowerQuotientMap_bijective f n :
  Function.Bijective
    (principalPowerIdealImageQuotientMap
      (algebraMap R (principalAdicCompletion f)) f n))
