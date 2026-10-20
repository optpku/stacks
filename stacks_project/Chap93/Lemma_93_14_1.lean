module

public import ReasLib.RingTheory.Algebra.FlatLift.Henselization
import StacksCheckRecall

/-!
# Flat algebra lifts versus pair henselization
-/

@[expose] public section

universe u

/- Lemma 93.14.1: for a surjection `A' → A` of Noetherian rings with nilpotent
kernel, a finite-type flat `A`-algebra `B`, and an ideal `b ⊆ B` such that
`Spec(B) ⟶ Spec(A)` is syntomic on the complement of `V(b)`, `B` has a flat
lift to `A'` if and only if the pair henselization
`henselizationRing (pairOfIdeal b)` has a flat lift to `A'`. -/
@[stacks 0DZB]
#check (Algebra.NilpotentLift.existsFlatLift_iff_existsFlatLift_henselization :
  ∀ {A' A B : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B] [IsNoetherianRing A'] [IsNoetherianRing A]
    [Algebra.FiniteType A B] [Module.Flat A B]
    [RingPairCat.henselianPairInclusion.IsRightAdjoint]
    (hsurj : Function.Surjective (algebraMap A' A))
    (hker : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (b : Ideal B) (hsyn : (algebraMap A B).SyntomicOnComplement b),
    Algebra.NilpotentLift.existsFlatLift A' A B ↔
      Algebra.NilpotentLift.existsFlatLift A' A
        (RingPairCat.henselizationRing (RingPairCat.pairOfIdeal b)))

end
