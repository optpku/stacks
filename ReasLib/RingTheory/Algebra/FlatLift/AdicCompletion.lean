module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.Algebra.FlatLift.Basic
public import ReasLib.RingTheory.RingHom.Syntomic.Complement

/-!
# Flat algebra lifts versus adic completion
-/

@[expose] public section

universe u

namespace Algebra.NilpotentLift

/-- For a surjection of Noetherian rings with nilpotent kernel, a finite-type
flat algebra, and an ideal on whose complement the algebra map is syntomic, a
flat lift exists if and only if the adic completion admits a flat lift. -/
theorem existsFlatLift_iff_existsFlatLift_adicCompletion
    {A' A B : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B] [IsNoetherianRing A'] [IsNoetherianRing A]
    [Algebra.FiniteType A B] [Module.Flat A B]
    (hsurj : Function.Surjective (algebraMap A' A))
    (hker : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (b : Ideal B) (hsyn : (algebraMap A B).SyntomicOnComplement b) :
    existsFlatLift A' A B ↔ existsFlatLift A' A (AdicCompletion b B) :=
  sorry

end Algebra.NilpotentLift

end
