module

public import ReasLib.CategoryTheory.Filtration.FiniteProjective

/-!
# Filtered finite projective objects

The filtered finite-projectivity predicate and its canonical instances are
available from their shared mathematical owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredObject
open scoped ZeroObject FilteredObject.Finite

universe u v

variable {R : Type u} [Ring R]

#check (CategoryTheory.FilteredObject.IsFilteredFiniteProjective :
    FilteredObject (ModuleCat.{v} R) → Prop)

#check (CategoryTheory.FilteredObject.isFilteredFiniteProjective_iff :
    ∀ {P : FilteredObject (ModuleCat.{v} R)},
      IsFilteredFiniteProjective P ↔ ∀ p, Module.FiniteProjective R (P.gradedPiece p))

#check (CategoryTheory.FilteredObject.IsFilteredFiniteProjective.of_iso :
    ∀ {P Q : FilteredObject (ModuleCat.{v} R)}
      (e : P ≅ Q) (hQ : IsFilteredFiniteProjective Q),
      IsFilteredFiniteProjective P)

#check (CategoryTheory.FilteredObject.instIsFilteredFiniteProjectiveZero :
    IsFilteredFiniteProjective (0 : FilteredObject (ModuleCat.{v} R)))

#check (CategoryTheory.FilteredObject.instFinite_gradedPiece :
    ∀ (P : FilteredObject (ModuleCat.{v} R)) [IsFilteredFiniteProjective P] (p : ℤ),
      Module.Finite R (P.gradedPiece p))

#check (CategoryTheory.FilteredObject.instProjective_gradedPiece :
    ∀ (P : FilteredObject (ModuleCat.{v} R)) [IsFilteredFiniteProjective P] (p : ℤ),
      Module.Projective R (P.gradedPiece p))

#check (CategoryTheory.FilteredObject.Finite.instFinite :
    ∀ (P : FilteredObject.Finite.category (ModuleCat.{v} R))
      [IsFilteredFiniteProjective P.obj],
      Module.Finite R ((FilteredObject.Finite.Forget.functor (ModuleCat.{v} R)).obj P))

#check (CategoryTheory.FilteredObject.Finite.instProjective :
    ∀ (P : FilteredObject.Finite.category (ModuleCat.{v} R))
      [IsFilteredFiniteProjective P.obj],
      Module.Projective R ((FilteredObject.Finite.Forget.functor (ModuleCat.{v} R)).obj P))
