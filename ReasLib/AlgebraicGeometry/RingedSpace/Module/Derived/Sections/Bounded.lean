module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Injective
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-below derived sections on open subsets

@stack 0717

This leaf specializes the canonical bounded-below right-derived-functor API to evaluation of
module sheaves on an open subset.  Its public surface hides the homotopy localization and
quasi-isomorphism denominator, which are implementation details of the generic owner.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Bounded

/-- The bounded-below total right-derived sections functor on an open subset. -/
@[stacks 0717 "bounded-below derived sections on an open subset"]
abbrev functor (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory.Plus X.Modules ⥤
      DerivedCategory.Plus (ModuleCat (sectionsRingOnOpen X U)) :=
  Functor.RightDerived.Bounded.functor (moduleSectionsEvaluationFunctor X U)

/-- The canonical localization unit for bounded-below derived sections. -/
noncomputable abbrev unit (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsEvaluationFunctor X U).toBoundedBelowDerived ⟶
      DerivedCategory.Plus.Qh ⋙ functor X U :=
  Functor.RightDerived.Bounded.unit (moduleSectionsEvaluationFunctor X U)

/-- Degree-`n` cohomology after bounded-below derived sections. -/
abbrev cohomologyFunctor (X : RingedSpace.{u}) (U : Opens X.carrier) (n : ℤ) :
    DerivedCategory.Plus X.Modules ⥤ ModuleCat (sectionsRingOnOpen X U) :=
  functor X U ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat (sectionsRingOnOpen X U)) n

/-- The degree-`n` cohomology object of bounded-below derived sections. -/
abbrev cohomology (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : DerivedCategory.Plus X.Modules) (n : ℤ) :
    ModuleCat (sectionsRingOnOpen X U) :=
  (cohomologyFunctor X U n).obj K

end AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Bounded

end
