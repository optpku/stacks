module

public import Mathlib.RingTheory.Jacobson.Ring
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.35.20
@stack 00GC

This item is the specialization of the finite-type Jacobson theorem to the
canonical Jacobson ring `ℤ`.
-/

universe u

section


variable {A : Type u} [CommRing A] [Algebra.FiniteType ℤ A]

/- Lemma 10.35.20: every finite type algebra over `ℤ` is a Jacobson ring.  The ambient
finite-type instance determines the specialization of the canonical theorem. -/
@[stacks 00GC]
#check (isJacobsonRing_of_finiteType : IsJacobsonRing A)

end

@[stacks 00GC "finite type over a Jacobson base"]
#check @isJacobsonRing_of_finiteType
