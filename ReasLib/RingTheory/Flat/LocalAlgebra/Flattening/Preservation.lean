module

public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.DirectLimit.Algebra.FlatLocus
public import ReasLib.RingTheory.Flat.Locus.Descent
public import ReasLib.RingTheory.Flat.LocalAlgebra.Flattening

/-!
# Preservation properties of the local-algebra flattening functor

This module records invariance under flat morphisms and preservation of filtered colimits for the
local-algebra flattening functor.
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace LocalAlgCat.Flattening

variable (A : Type u) (B : Type v) (M : Type w)
variable [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [AddCommGroup M] [Module B M]

namespace IsFlatAtClosedPoint

/-- Closed-point flatness is equivalent across a flat morphism of local `A`-algebras. -/
theorem iff_of_flat {T U : LocalAlgCat.{v} A} (f : T ⟶ U)
    (hflat : (LocalAlgCat.Hom.toLocal A f).hom.toRingHom.Flat) :
    IsFlatAtClosedPoint A B M T ↔ IsFlatAtClosedPoint A B M U := sorry

end IsFlatAtClosedPoint

/-- A flat morphism of local `A`-algebras induces a bijection between the corresponding fibers of
the flattening functor. -/
theorem map_bijective_of_flat {T U : LocalAlgCat.{v} A} (f : T ⟶ U)
    (hflat : (LocalAlgCat.Hom.toLocal A f).hom.toRingHom.Flat) :
    Function.Bijective ((functor A B M).map f) := sorry

/-- The flattening functor preserves filtered colimits when the algebra and module satisfy the
corresponding finite-presentation hypotheses. -/
instance preservesFilteredColimits [Algebra.EssFinitePresentation A B]
    [Module.FinitePresentation B M] :
    PreservesFilteredColimits (functor A B M) := sorry

end LocalAlgCat.Flattening
