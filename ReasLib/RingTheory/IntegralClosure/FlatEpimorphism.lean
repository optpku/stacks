module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import ReasLib.RingTheory.Algebra.IsEpi.TensorSquare
public import ReasLib.RingTheory.WeakDimension
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Integral closure along flat injective epimorphisms

A flat injective ring epimorphism out of a ring of weak dimension at most one
has no new integral elements.

@stack 092V
-/

universe u v

namespace Algebra.IsEpi

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Lemma 15.105.21: a flat injective epimorphism from a ring of weak dimension at most one
exhibits the source as integrally closed in the target. -/
@[stacks 092V "Lemma 15.105.21"]
theorem isIntegrallyClosedIn_of_flat_of_injective_of_weakDimensionLE_one
    (hwd : HasWeakDimensionLE A 1) (hflat : Module.Flat A B)
    (hinj : Function.Injective (algebraMap A B)) (hEpi : Algebra.IsEpi A B) :
    IsIntegrallyClosedIn A B := sorry

end Algebra.IsEpi
