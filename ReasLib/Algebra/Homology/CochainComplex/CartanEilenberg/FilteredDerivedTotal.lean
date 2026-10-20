/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.DerivedTotal
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration

/-!
# Filtered Cartan--Eilenberg Abutment Comparisons

This leaf identifies the cohomology of either standard filtered total of a mapped
Cartan--Eilenberg resolution with the cohomology of the corresponding total right-derived value.
The unfiltered comparison remains in `DerivedTotal`.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex₂

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {K : CochainComplex.Plus A} (I : CartanEilenbergResolution K)
variable (F : A ⥤ B) [F.Additive] [HasDerivedCategory.{w} B]
variable {E : Type u₃} [Category.{v₃} E]
variable (Q : HomotopyCategory.Plus A ⥤ E)
variable [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
variable [Functor.RightDerived.EverywhereDefined F.toBoundedBelowDerived
  (HomotopyCategory.Plus.quasiIso A)]

namespace First

/-- The cohomology of the first filtered total of a mapped Cartan--Eilenberg resolution
computes the cohomology of the total right-derived value. -/
@[stacks 015J "first filtered Cartan-Eilenberg total abutment"]
noncomputable def filteredTotalHomologyIso (n : ℤ) :
    (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F)).underlying.homology n ≅
      Functor.RightDerived.Bounded.cohomology F Q K n :=
  (HomologicalComplex.homologyFunctor B (up ℤ) n).mapIso
      (eqToIso (HomologicalComplex₂.First.Filtration.total_underlying (I.mapBicomplex F))) ≪≫
    MappedTotal.homologyIso I F Q n

/-- The forward first-filtered abutment comparison first forgets the filtration and then uses
the total right-derived comparison. -/
@[simp]
theorem filteredTotalHomologyIso_hom (n : ℤ) :
    (filteredTotalHomologyIso I F Q n).hom =
      (HomologicalComplex.homologyFunctor B (up ℤ) n).map
          (eqToIso (HomologicalComplex₂.First.Filtration.total_underlying (I.mapBicomplex F))).hom ≫
        (MappedTotal.homologyIso I F Q n).hom := sorry

/-- The inverse first-filtered abutment comparison first uses the inverse total right-derived
comparison and then restores the filtered-total presentation. -/
@[simp]
theorem filteredTotalHomologyIso_inv (n : ℤ) :
    (filteredTotalHomologyIso I F Q n).inv =
      (MappedTotal.homologyIso I F Q n).inv ≫
        (HomologicalComplex.homologyFunctor B (up ℤ) n).map
          (eqToIso (HomologicalComplex₂.First.Filtration.total_underlying (I.mapBicomplex F))).inv := sorry

end First

namespace Second

/-- The cohomology of the second filtered total of a mapped Cartan--Eilenberg resolution
computes the cohomology of the same total right-derived value. -/
@[stacks 015J "second filtered Cartan-Eilenberg total abutment"]
noncomputable def filteredTotalHomologyIso (n : ℤ) :
    (HomologicalComplex₂.Second.Filtration.total (I.mapBicomplex F)).underlying.homology n ≅
      Functor.RightDerived.Bounded.cohomology F Q K n :=
  (HomologicalComplex.homologyFunctor B (up ℤ) n).mapIso
      (eqToIso (HomologicalComplex₂.Second.Filtration.total_underlying (I.mapBicomplex F))) ≪≫
    MappedTotal.homologyIso I F Q n

/-- The forward second-filtered abutment comparison first forgets the filtration and then uses
the total right-derived comparison. -/
@[simp]
theorem filteredTotalHomologyIso_hom (n : ℤ) :
    (filteredTotalHomologyIso I F Q n).hom =
      (HomologicalComplex.homologyFunctor B (up ℤ) n).map
          (eqToIso (HomologicalComplex₂.Second.Filtration.total_underlying (I.mapBicomplex F))).hom ≫
        (MappedTotal.homologyIso I F Q n).hom := sorry

/-- The inverse second-filtered abutment comparison first uses the inverse total right-derived
comparison and then restores the filtered-total presentation. -/
@[simp]
theorem filteredTotalHomologyIso_inv (n : ℤ) :
    (filteredTotalHomologyIso I F Q n).inv =
      (MappedTotal.homologyIso I F Q n).inv ≫
        (HomologicalComplex.homologyFunctor B (up ℤ) n).map
          (eqToIso (HomologicalComplex₂.Second.Filtration.total_underlying (I.mapBicomplex F))).inv := sorry

end Second

end CochainComplex.CartanEilenbergResolution
