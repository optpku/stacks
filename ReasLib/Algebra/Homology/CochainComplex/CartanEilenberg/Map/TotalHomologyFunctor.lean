/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.TotalFunctor
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.TotalHomology

/-!
# Homology functors of Cartan--Eilenberg totals

Mapped-total cohomology and both filtered-total cohomologies are functors on bundled
Cartan--Eilenberg resolutions.  This neutral leaf does not import derived-category comparisons.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive]

/-- Cohomology of the mapped total, functorial in a bundled Cartan--Eilenberg resolution. -/
@[stacks 015J "mapped-total cohomology functor of Cartan-Eilenberg resolutions"]
noncomputable abbrev mappedTotalHomology (n : ℤ) : Bundled A ⥤ B :=
  mappedTotal F ⋙ HomologicalComplex.homologyFunctor B (up ℤ) n

/-- Object computation for mapped-total cohomology. -/
@[simp, stacks 015J "mapped-total cohomology functor of Cartan-Eilenberg resolutions"]
theorem mappedTotalHomology_obj (n : ℤ) (X : Bundled A) :
    (mappedTotalHomology F n).obj X =
      HomologicalComplex.homology ((X.resolution.mapBicomplex F).total (up ℤ)) n := sorry

/-- Morphism computation for mapped-total cohomology. -/
@[simp, stacks 015J "mapped-total cohomology functor of Cartan-Eilenberg resolutions"]
theorem mappedTotalHomology_map (n : ℤ) {X Y : Bundled A} (f : X ⟶ Y) :
    (mappedTotalHomology F n).map f = Map.mappedTotalHomology f F n := sorry

namespace First

/-- Cohomology of the underlying first-filtered total, functorial in a bundled
Cartan--Eilenberg resolution. -/
@[stacks 015J "first-filtered abutment functor of Cartan-Eilenberg resolutions"]
noncomputable abbrev filteredTotalHomology (n : ℤ) : Bundled A ⥤ B :=
  First.filteredTotal F ⋙ FilteredComplex.underlyingFunctor ⋙
    HomologicalComplex.homologyFunctor B (up ℤ) n

/-- Object computation for first-filtered total cohomology. -/
@[simp, stacks 015J "first-filtered abutment functor of Cartan-Eilenberg resolutions"]
theorem filteredTotalHomology_obj (n : ℤ) (X : Bundled A) :
    (filteredTotalHomology F n).obj X =
      HomologicalComplex.homology
        (HomologicalComplex₂.First.Filtration.total
          (X.resolution.mapBicomplex F)).underlying n := sorry

/-- Morphism computation for first-filtered total cohomology. -/
@[simp, stacks 015J "first-filtered abutment functor of Cartan-Eilenberg resolutions"]
theorem filteredTotalHomology_map (n : ℤ) {X Y : Bundled A} (f : X ⟶ Y) :
    (filteredTotalHomology F n).map f =
      Map.First.filteredTotalHomology f F n := sorry

/-- Forgetting the first filtration does not change the mapped-total homology functor. -/
@[simp, stacks 015J "underlying first-filtered homology functor of Cartan-Eilenberg resolutions"]
theorem filteredTotalHomology_eq_mapped (n : ℤ) :
    filteredTotalHomology F n = mappedTotalHomology F n := sorry

end First

namespace Second

/-- Cohomology of the underlying second-filtered total, functorial in a bundled
Cartan--Eilenberg resolution. -/
@[stacks 015J "second-filtered abutment functor of Cartan-Eilenberg resolutions"]
noncomputable abbrev filteredTotalHomology (n : ℤ) : Bundled A ⥤ B :=
  Second.filteredTotal F ⋙ FilteredComplex.underlyingFunctor ⋙
    HomologicalComplex.homologyFunctor B (up ℤ) n

/-- Object computation for second-filtered total cohomology. -/
@[simp, stacks 015J "second-filtered abutment functor of Cartan-Eilenberg resolutions"]
theorem filteredTotalHomology_obj (n : ℤ) (X : Bundled A) :
    (filteredTotalHomology F n).obj X =
      HomologicalComplex.homology
        (HomologicalComplex₂.Second.Filtration.total
          (X.resolution.mapBicomplex F)).underlying n := sorry

/-- Morphism computation for second-filtered total cohomology. -/
@[simp, stacks 015J "second-filtered abutment functor of Cartan-Eilenberg resolutions"]
theorem filteredTotalHomology_map (n : ℤ) {X Y : Bundled A} (f : X ⟶ Y) :
    (filteredTotalHomology F n).map f =
      Map.Second.filteredTotalHomology f F n := sorry

/-- Forgetting the second filtration does not change the mapped-total homology functor. -/
@[simp, stacks 015J "underlying second-filtered homology functor of Cartan-Eilenberg resolutions"]
theorem filteredTotalHomology_eq_mapped (n : ℤ) :
    filteredTotalHomology F n = mappedTotalHomology F n := sorry

end Second

end CochainComplex.CartanEilenbergResolution.Bundled
