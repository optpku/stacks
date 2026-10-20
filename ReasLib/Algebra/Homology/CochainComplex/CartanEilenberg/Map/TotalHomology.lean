/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Total

/-!
# Homology maps of Cartan--Eilenberg totals

Maps of Cartan--Eilenberg resolutions induce maps on mapped-total cohomology and on the
cohomology of either filtered total.  These constructions are independent of derived-category
comparisons and therefore live in this neutral leaf.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {K L M : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}
variable {N : CartanEilenbergResolution M}

/-- The map induced on the cohomology of a mapped Cartan--Eilenberg total. -/
@[stacks 015J "map on a Cartan-Eilenberg mapped-total abutment"]
noncomputable abbrev mappedTotalHomology
    (f : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    HomologicalComplex.homology ((I.mapBicomplex F).total (up ℤ)) n ⟶
      HomologicalComplex.homology ((J.mapBicomplex F).total (up ℤ)) n :=
  HomologicalComplex.homologyMap (mappedTotal f F) n

/-- Mapped-total cohomology preserves identity maps of Cartan--Eilenberg resolutions. -/
@[simp]
theorem mappedTotalHomology_id
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    mappedTotalHomology (id I) F n = 𝟙 _ := sorry

/-- Mapped-total cohomology preserves composition of Cartan--Eilenberg resolution maps. -/
@[stacks 015J "composition law for Cartan-Eilenberg mapped-total abutment maps", simp,
  reassoc]
theorem mappedTotalHomology_comp (f : Map I J) (g : Map J N)
    (F : A ⥤ B) [F.Additive] (n : ℤ) :
    mappedTotalHomology (comp f g) F n =
      mappedTotalHomology f F n ≫ mappedTotalHomology g F n := sorry

namespace First

/-- The map on the cohomology of the underlying first-filtered total. -/
@[stacks 015J "map on the first Cartan-Eilenberg filtered abutment"]
noncomputable abbrev filteredTotalHomology
    (f : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    (HomologicalComplex₂.First.Filtration.total
      (I.mapBicomplex F)).underlying.homology n ⟶
      (HomologicalComplex₂.First.Filtration.total
        (J.mapBicomplex F)).underlying.homology n :=
  HomologicalComplex.homologyMap
    (FilteredComplex.underlyingMap (First.filteredTotal f F)) n

/-- Forgetting the first filtration identifies its homology map with mapped-total homology. -/
@[simp]
theorem filteredTotalHomology_eq_mapped
    (f : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology f F n = mappedTotalHomology f F n := sorry

/-- The map on first-filtered total cohomology preserves identity maps. -/
@[simp]
theorem filteredTotalHomology_id
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (id I) F n = 𝟙 _ := sorry

/-- The map on first-filtered total cohomology preserves composition. -/
@[stacks 015J "composition law for first-filtered Cartan-Eilenberg abutment maps", simp,
  reassoc]
theorem filteredTotalHomology_comp (f : Map I J) (g : Map J N)
    (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (comp f g) F n =
      filteredTotalHomology f F n ≫ filteredTotalHomology g F n := sorry

end First

namespace Second

/-- The map on the cohomology of the underlying second-filtered total. -/
@[stacks 015J "map on the second Cartan-Eilenberg filtered abutment"]
noncomputable abbrev filteredTotalHomology
    (f : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    (HomologicalComplex₂.Second.Filtration.total
      (I.mapBicomplex F)).underlying.homology n ⟶
      (HomologicalComplex₂.Second.Filtration.total
        (J.mapBicomplex F)).underlying.homology n :=
  HomologicalComplex.homologyMap
    (FilteredComplex.underlyingMap (Second.filteredTotal f F)) n

/-- Forgetting the second filtration identifies its homology map with mapped-total homology. -/
@[simp]
theorem filteredTotalHomology_eq_mapped
    (f : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology f F n = mappedTotalHomology f F n := sorry

/-- The map on second-filtered total cohomology preserves identity maps. -/
@[simp]
theorem filteredTotalHomology_id
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (id I) F n = 𝟙 _ := sorry

/-- The map on second-filtered total cohomology preserves composition. -/
@[stacks 015J "composition law for second-filtered Cartan-Eilenberg abutment maps", simp,
  reassoc]
theorem filteredTotalHomology_comp (f : Map I J) (g : Map J N)
    (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (comp f g) F n =
      filteredTotalHomology f F n ≫ filteredTotalHomology g F n := sorry

end Second

end CochainComplex.CartanEilenbergResolution.Map
