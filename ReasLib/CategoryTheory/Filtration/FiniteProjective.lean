module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.RingTheory.Finiteness.Projective
public import ReasLib.CategoryTheory.Filtration.GradedPiece
public import ReasLib.CategoryTheory.Filtration.ZeroObject

/-!
# Filtered finite projective objects

A filtered left module is filtered finite projective when all its associated
graded pieces are finite projective. Graded pieces and the underlying module of
a finite filtered finite-projective object are finite and projective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject FilteredObject.Finite

universe u v

namespace CategoryTheory.FilteredObject

variable {R : Type u} [Ring R]

/-- A filtered left `R`-module is filtered finite projective when every associated
graded piece is a finite projective `R`-module. -/
class IsFilteredFiniteProjective (P : FilteredObject (ModuleCat.{v} R)) : Prop where
  /-- Every graded piece of a filtered finite-projective object is finite projective. -/
  finiteProjective (p : ℤ) : Module.FiniteProjective R (P.gradedPiece p)

/-- Filtered finite-projectivity is equivalent to finite projectivity of every
associated graded piece. -/
theorem isFilteredFiniteProjective_iff {P : FilteredObject (ModuleCat.{v} R)} :
    IsFilteredFiniteProjective P ↔ ∀ p, Module.FiniteProjective R (P.gradedPiece p) :=
  sorry

/-- Filtered finite-projectivity transports across an isomorphism of filtered objects. -/
theorem IsFilteredFiniteProjective.of_iso {P Q : FilteredObject (ModuleCat.{v} R)}
    (e : P ≅ Q) (hQ : IsFilteredFiniteProjective Q) :
    IsFilteredFiniteProjective P := sorry

/-- The zero filtered module is filtered finite projective. -/
noncomputable instance instIsFilteredFiniteProjectiveZero :
    IsFilteredFiniteProjective (0 : FilteredObject (ModuleCat.{v} R)) := sorry

/-- Graded pieces of a filtered finite-projective object are finite modules. -/
instance instFinite_gradedPiece (P : FilteredObject (ModuleCat.{v} R))
    [IsFilteredFiniteProjective P] (p : ℤ) :
    Module.Finite R (P.gradedPiece p) := sorry

/-- Graded pieces of a filtered finite-projective object are projective modules. -/
instance instProjective_gradedPiece (P : FilteredObject (ModuleCat.{v} R))
    [IsFilteredFiniteProjective P] (p : ℤ) :
    Module.Projective R (P.gradedPiece p) := sorry

namespace Finite

/-- The underlying module of a finite filtered finite-projective object is finite. -/
instance instFinite (P : category (ModuleCat.{v} R))
    [IsFilteredFiniteProjective P.obj] :
    Module.Finite R ((Forget.functor (ModuleCat.{v} R)).obj P) := sorry

/-- The underlying module of a finite filtered finite-projective object is projective. -/
instance instProjective (P : category (ModuleCat.{v} R))
    [IsFilteredFiniteProjective P.obj] :
    Module.Projective R ((Forget.functor (ModuleCat.{v} R)).obj P) := sorry

end Finite

end CategoryTheory.FilteredObject
