/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.AlgebraicGeometry.PrimeSpectrum.Notation
public import ReasLib.RingTheory.Henselian.Pair.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Integral base change for pair Henselization

This file owns the tensor comparison from the base change of a pair Henselization to the
Henselization of the target pair.

@stack 0DYE
-/

@[expose] public section

open PrimeSpectrum
open scoped PrimeSpectrum TensorProduct

universe u

noncomputable section

-- Local instance justification (instance diamond): select both canonical tensor-factor algebra
-- structures only while expressing henselian-pair base change.
attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

namespace RingPairCat

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A) (J : Ideal B)
variable [henselianPairInclusion.IsRightAdjoint]

/-- The Henselization of `(B, J)` carries the composite `A`-algebra structure. -/
@[stacks 0DYE "composite algebra structure on the target pair Henselization"]
instance pairOfIdeal_henselizationRing_comp_algebra :
    Algebra A (henselizationRing (pairOfIdeal J)) :=
  (RingHom.comp (toHenselization (pairOfIdeal J)) (algebraMap A B)).toAlgebra

/-- The composite `A → B → B^h` is the canonical scalar tower on a pair Henselization. -/
@[stacks 0DYE "scalar tower on the target pair Henselization"]
instance pairOfIdeal_henselizationRing_isScalarTower :
    IsScalarTower A B (henselizationRing (pairOfIdeal J)) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The map on Henselization rings induced by a map of pairs commutes with the original
`A`-algebra maps. -/
theorem henselizationRingMap_commutes
    (hIJ : I ≤ Ideal.comap (algebraMap A B) J) (a : A) :
    henselizationRingMap (pairOfIdealMap I J hIJ)
        (algebraMap A (henselizationRing (pairOfIdeal I)) a) =
      algebraMap A (henselizationRing (pairOfIdeal J)) a := sorry

/-- The canonical tensor comparison `A^h ⊗[A] B →ₐ[A] B^h` attached to a map of pairs. -/
@[stacks 0DYE "Henselization tensor comparison"]
abbrev henselizationBaseChangeComparison
    (hIJ : I ≤ Ideal.comap (algebraMap A B) J) :
    (henselizationRing (pairOfIdeal I) ⊗[A] B) →ₐ[A]
      henselizationRing (pairOfIdeal J) :=
  Algebra.TensorProduct.productMap
    { toRingHom := henselizationRingMap (pairOfIdealMap I J hIJ)
      commutes' := henselizationRingMap_commutes I J hIJ }
    ((Algebra.ofId B (henselizationRing (pairOfIdeal J))).restrictScalars A)

/-- Lemma 15.12.7: under equal target zero loci and an integral map `A → B`, the tensor
comparison is bijective. -/
@[stacks 0DYE "Lemma 15.12.7"]
theorem henselizationBaseChangeComparison_bijective_of_isIntegral
    (hIJ : I ≤ Ideal.comap (algebraMap A B) J)
    (hV : V((J : Set B)) = V((Ideal.map (algebraMap A B) I : Set B)))
    [Algebra.IsIntegral A B] :
    Function.Bijective (henselizationBaseChangeComparison I J hIJ) := sorry

end RingPairCat
