/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.SquareZeroLift
public import ReasLib.RingTheory.Extension.Presentation.SquareZero

/-!
# Presentation classes detected by square-zero lifting obstructions

The obstruction of a lifted differential first gives a map from second homology of the
kernel-annihilator quotient to its zeroth homology.  An augmentation identifies the latter with
the corresponding quotient of the presented algebra.  This file owns that composite and the
presentation-level realization theorem; the quotient DGA and augmentation constructions remain
in their generic algebraic leaves.
-/

@[expose] public section

noncomputable section

open CategoryTheory.Limits
open RingHom.SquareZeroExtension

universe u v w x y

namespace DividedPowerChainAlgebra.SquareZeroLift

variable {R' R : Type u} [CommRing R'] [CommRing R]
variable {S : Type y} [CommRing S] [Algebra R S]
variable {f : R' →+* R} [f.IsSquareZeroExtension]
variable {generators : ℕ → Type v}
variable {A : DividedPowerChainAlgebra.{u, y} R} {g : Generator f}
variable {P : A.toGradedAlgebra.FreePresentation generators}
variable {ι : Type w} {σ : Type x} [Fintype σ]

/-- The square-zero lifting map from second homology to the presented algebra modulo the extended
kernel annihilator. -/
@[stacks 09PT "square-zero obstruction map to the augmentation quotient"]
def theta (L : A.SquareZeroLift g P)
    (augmentation : ChainDGAlgebra.Augmentation A.toChainDGAlgebra S) :
    (A.annihilatorQuotient (f := f)).homology 2 →ₗ[R ⧸ kernelAnnihilator f]
      kernelAnnihilatorQuotient f S :=
  (augmentation.nonnegativeModel.quotientHomologyZeroMap
      (kernelAnnihilator f)).toLinearMap.comp L.obstructionHomologyMap

/-- The square-zero obstruction map is the obstruction on homology followed by the quotient
augmentation. -/
@[simp]
theorem theta_apply (L : A.SquareZeroLift g P)
    (augmentation : ChainDGAlgebra.Augmentation A.toChainDGAlgebra S)
    (ξ : (A.annihilatorQuotient (f := f)).homology 2) :
    L.theta augmentation ξ =
      augmentation.nonnegativeModel.quotientHomologyZeroMap
        (kernelAnnihilator f) (L.obstructionHomologyMap ξ) := sorry

/-- On a degree-two cycle class, `theta` is represented by the obstruction derivation followed by
the quotient augmentation in degree zero. -/
theorem theta_homologyπ (L : A.SquareZeroLift g P)
    (augmentation : ChainDGAlgebra.Augmentation A.toChainDGAlgebra S)
    (x : (A.annihilatorQuotient (f := f)).cycles 2) :
    L.theta augmentation
        ((A.annihilatorQuotient (f := f)).homologyπ 2 x) =
      augmentation.nonnegativeModel.quotientHomologyZeroMap
        (kernelAnnihilator f)
        ((A.annihilatorQuotient (f := f)).homologyπ 0
          (ChainGradedAlgebra.Derivation.cyclesMapTo L.chainObstruction
            L.chainObstruction_isClosed obstructionHomologyDegree x)) := sorry

/-- For an explicit square-zero lift, a lifted presentation relation whose coefficients lie in
the kernel annihilator is realized by a class in `H₂(A / IA)`. -/
theorem exists_homologyClass (L : A.SquareZeroLift g P)
    (augmentation : ChainDGAlgebra.Augmentation A.toChainDGAlgebra S)
    (hH0 : Function.Bijective augmentation.homologyZeroMap)
    (hH1 : IsZero (A.toChainDGAlgebra.homology 1))
    {Q : Algebra.Presentation R S ι σ}
    (relation : Algebra.Presentation.LiftedRelation g Q) :
    ∃ ξ : (A.annihilatorQuotient (f := f)).homology 2,
      L.theta augmentation ξ = relation.obstruction := sorry

/-- Lemma 23.7.2 (Tag 09PT): under the finite free setup of Lemma 23.7.1, if an augmentation
identifies `H₀(A)` with a presented `R`-algebra `S` and `H₁(A) = 0`, then every lifted relation
whose coefficients lie in the kernel annihilator is the `theta`-image of a class in
`H₂(A / IA)`. -/
@[stacks 09PT "Lemma 23.7.2"]
theorem exists_homologyClass_of_finite (L : A.SquareZeroLift g P)
    (h_finite : ∀ n : ℕ, Finite (generators n))
    (augmentation : ChainDGAlgebra.Augmentation A.toChainDGAlgebra S)
    (hH0 : Function.Bijective augmentation.homologyZeroMap)
    (hH1 : IsZero (A.toChainDGAlgebra.homology 1))
    {Q : Algebra.Presentation R S ι σ}
    (relation : Algebra.Presentation.LiftedRelation g Q) :
    ∃ ξ : (A.annihilatorQuotient (f := f)).homology 2,
      L.theta augmentation ξ = relation.obstruction := sorry

/-- Combining finite free lift existence with `exists_homologyClass` produces a lift and a
homology class realizing the presentation obstruction. -/
theorem exists_lift_and_homologyClass (A : DividedPowerChainAlgebra.{u, y} R) (g : Generator f)
    (P : A.toGradedAlgebra.FreePresentation generators)
    (h_finite : ∀ n : ℕ, Finite (generators n))
    (augmentation : ChainDGAlgebra.Augmentation A.toChainDGAlgebra S)
    (hH0 : Function.Bijective augmentation.homologyZeroMap)
    (hH1 : IsZero (A.toChainDGAlgebra.homology 1))
    {Q : Algebra.Presentation R S ι σ}
    (relation : Algebra.Presentation.LiftedRelation g Q) :
    ∃ (L : A.SquareZeroLift g P)
      (ξ : (A.annihilatorQuotient (f := f)).homology 2),
      L.theta augmentation ξ = relation.obstruction := sorry

end DividedPowerChainAlgebra.SquareZeroLift
