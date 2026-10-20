module

public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Quotients of Finite Filtered Objects

This is the data layer for the derived category of finite filtered objects.  It uses Mathlib's
canonical localization carrier and quotient functor for `FilteredObject.Finite.Homotopy.quasiIso`; triangulated enhancements
belong to `Derived.Triangulated`, whose additional exact-category input is genuinely separate.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasCokernels C] [CategoryWithHomology (GradedObject ℤ C)]

namespace Quotient

/-- The `05S2` derived category of finite filtered objects: the canonical localization of finite
filtered homotopy complexes at finite filtered quasi-isomorphisms. -/
@[stacks 05S2 "finite filtered derived category"]
abbrev Category : Type (max u v) :=
  (FilteredObject.Finite.Homotopy.quasiIso C).Localization

/-- The `05S2` quotient functor from finite filtered homotopy complexes to their canonical
derived localization. -/
@[stacks 05S2 "finite filtered derived quotient functor"]
abbrev functor :
    HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ) ⥤ Category C :=
  (FilteredObject.Finite.Homotopy.quasiIso C).Q

/-- The canonical finite filtered derived quotient localizes precisely at finite filtered
quasi-isomorphisms. -/
@[stacks 05S2 "finite filtered derived quotient functor"]
instance isLocalization :
    Functor.IsLocalization (functor C) (FilteredObject.Finite.Homotopy.quasiIso C) :=
  inferInstance

end Quotient

end CategoryTheory.FilteredObject.FiniteDerived
