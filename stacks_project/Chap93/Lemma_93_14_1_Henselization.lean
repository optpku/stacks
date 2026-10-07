module

public import ReasLib.RingTheory.Henselian.Pair.BaseChange
public import stacks_project.Chap93.Lemma_93_12_3_Lift

/-!
# Flat algebra lifts versus pair henselization

This leaf compares existence of an `A'`-flat algebra lift of `B` with existence
of an `A'`-flat algebra lift of the pair henselization of `(B, b)`.
-/

@[expose] public section

universe u

noncomputable section

open RingPairCat

namespace Algebra.NilpotentLift

/-- For a surjection of Noetherian rings with nilpotent kernel, a finite-type
flat algebra, and an ideal on whose complement the algebra map is syntomic, a
flat lift exists if and only if the pair henselization admits a flat lift. -/
theorem existsFlatLift_iff_existsFlatLift_henselization
    {A' A B : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B] [IsNoetherianRing A'] [IsNoetherianRing A]
    [Algebra.FiniteType A B] [Module.Flat A B]
    [henselianPairInclusion.IsRightAdjoint]
    (hsurj : Function.Surjective (algebraMap A' A))
    (hker : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (b : Ideal B) (hsyn : (algebraMap A B).SyntomicOnComplement b) :
    existsFlatLift A' A B ↔
      existsFlatLift A' A (henselizationRing (pairOfIdeal b)) :=
  sorry

end Algebra.NilpotentLift

end
