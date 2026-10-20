module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.FiniteType
public import ReasLib.RingTheory.AdicCompletion.RigSmooth
public import ReasLib.RingTheory.Ideal.OneAdd
public import ReasLib.RingTheory.Smooth.Complement

/-!
# Rig-smooth completions of finite-type algebras

Smoothness over an ideal complement implies rig-smoothness of the completion.
Conversely, a rig-smooth completion gives smoothness over the same complement
after localization at an element of `1 + I B`.
-/

@[expose] public section

universe u

namespace Algebra.RigSmooth

/-- The completion of a finite-type algebra over a Noetherian ring is rig-smooth
over `(A, I)` if the algebra is smooth over the complement of `V(I)`. -/
@[stacks 0GAK]
theorem of_isSmoothOverComplement {A B : Type u} [CommRing A]
    [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (I : Ideal A) (h : IsSmoothOverComplement I B) :
    RigSmooth I (AdicCompletion (I.map (algebraMap A B)) B) :=
  sorry

/-- If the completion of a finite-type algebra over a Noetherian ring is
rig-smooth over `(A, I)`, there is an element of `1 + I B` whose principal
localization is smooth over the complement of `V(I)`. -/
@[stacks 0GAK]
theorem exists_mem_oneAdd_isSmoothOverComplement {A B : Type u} [CommRing A]
    [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (I : Ideal A) [RigSmooth I (AdicCompletion (I.map (algebraMap A B)) B)] :
    ∃ g : B, g ∈ (I.map (algebraMap A B)).oneAdd ∧
      IsSmoothOverComplement I (Localization.Away g) :=
  sorry

end Algebra.RigSmooth
