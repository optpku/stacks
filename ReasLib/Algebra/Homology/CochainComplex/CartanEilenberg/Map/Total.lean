/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Functor
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.TotalFunctoriality
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration

/-!
# Total maps of Cartan--Eilenberg resolutions

Maps of Cartan--Eilenberg resolutions induce maps of raw totals, mapped totals, and both standard
filtered totals.  This leaf also records the augmentation squares and the identity/composition
API needed by downstream functoriality arguments.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex₂

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {K L M : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}
variable {N : CartanEilenbergResolution M}

/-- The map on total cochain complexes induced by a map of Cartan--Eilenberg resolutions. -/
@[stacks 015J "total map of Cartan-Eilenberg resolutions"]
noncomputable abbrev total (f : Map I J) : Total.complex I ⟶ Total.complex J :=
  HomologicalComplex₂.total.map f.hom (up ℤ)

/-- The total map bundled as a map of bounded-below cochain complexes. -/
@[stacks 015J "bounded-below total map of Cartan-Eilenberg resolutions"]
noncomputable def totalPlus (f : Map I J) : Total.toPlus I ⟶ Total.toPlus J :=
  ⟨total f⟩

/-- Forgetting the bounded-below structure from a total map recovers its underlying total
cochain-complex map. -/
@[simp]
theorem totalPlus_hom (f : Map I J) : (totalPlus f).hom = total f := sorry

/-- The augmentation to the total complex is natural in maps of Cartan--Eilenberg
resolutions. -/
@[stacks 015J "naturality of the Cartan-Eilenberg total augmentation", reassoc]
theorem totalAugmentation_naturality (f : Map I J) :
    Total.augmentation I ≫ total f = f.base.hom ≫ Total.augmentation J := sorry

/-- Totalization sends the identity resolution map to the identity. -/
@[simp]
theorem total_id (I : CartanEilenbergResolution K) :
    total (id I) = 𝟙 (Total.complex I) := sorry

/-- Totalization sends a composite resolution map to the composite total map. -/
@[simp, reassoc]
theorem total_comp (f : Map I J) (g : Map J N) :
    total (comp f g) = total f ≫ total g := sorry

/-- The bounded-below total construction preserves identity maps. -/
@[simp]
theorem totalPlus_id (I : CartanEilenbergResolution K) :
    totalPlus (id I) = 𝟙 (Total.toPlus I) := sorry

/-- The bounded-below total construction preserves composition. -/
@[stacks 015J "composition law for bounded-below Cartan-Eilenberg total maps", simp, reassoc]
theorem totalPlus_comp (f : Map I J) (g : Map J N) :
    totalPlus (comp f g) = totalPlus f ≫ totalPlus g := sorry

section Mapped

variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- The map on totals after applying an additive functor termwise. -/
@[stacks 015J "mapped total map of Cartan-Eilenberg resolutions"]
noncomputable abbrev mappedTotal (f : Map I J) (F : A ⥤ B) [F.Additive] :
    (I.mapBicomplex F).total (up ℤ) ⟶ (J.mapBicomplex F).total (up ℤ) :=
  HomologicalComplex₂.total.map (mapped f F) (up ℤ)

/-- The mapped augmentation to the total complex is natural in maps of
Cartan--Eilenberg resolutions. -/
@[stacks 015J "naturality of the mapped Cartan-Eilenberg total augmentation", reassoc]
theorem mappedAugmentation_naturality
    (f : Map I J) (F : A ⥤ B) [F.Additive] :
    MappedTotal.augmentation I F ≫ mappedTotal f F =
      (F.mapHomologicalComplex (up ℤ)).map f.base.hom ≫
        MappedTotal.augmentation J F := sorry

/-- The mapped total map is the totalization of the mapped identity resolution map. -/
@[simp]
theorem mappedTotal_id (I : CartanEilenbergResolution K)
    (F : A ⥤ B) [F.Additive] :
    mappedTotal (id I) F = 𝟙 ((I.mapBicomplex F).total (up ℤ)) := sorry

/-- The mapped total construction preserves composition. -/
@[simp, reassoc]
theorem mappedTotal_comp (f : Map I J) (g : Map J N)
    (F : A ⥤ B) [F.Additive] :
    mappedTotal (comp f g) F = mappedTotal f F ≫ mappedTotal g F := sorry

namespace First

/-- The induced map between the first-filtered mapped totals. -/
@[stacks 015J "first-filtered Cartan-Eilenberg total map"]
noncomputable abbrev filteredTotal
    (f : Map I J) (F : A ⥤ B) [F.Additive] :
    HomologicalComplex₂.First.Filtration.total (I.mapBicomplex F) ⟶
      HomologicalComplex₂.First.Filtration.total (J.mapBicomplex F) :=
  HomologicalComplex₂.First.Filtration.Map.hom (mapped f F)

/-- Forgetting the first filtration recovers the mapped total map. -/
@[simp]
theorem filteredTotal_underlying
    (f : Map I J) (F : A ⥤ B) [F.Additive] :
    FilteredComplex.underlyingMap (filteredTotal f F) = mappedTotal f F := sorry

/-- The first-filtered total construction preserves identity maps. -/
@[simp]
theorem filteredTotal_id (I : CartanEilenbergResolution K)
    (F : A ⥤ B) [F.Additive] :
    filteredTotal (id I) F = 𝟙 _ := sorry

/-- The first-filtered total construction preserves composition. -/
@[simp, reassoc]
theorem filteredTotal_comp (f : Map I J) (g : Map J N)
    (F : A ⥤ B) [F.Additive] :
    filteredTotal (comp f g) F = filteredTotal f F ≫ filteredTotal g F := sorry

end First

namespace Second

/-- The induced map between the second-filtered mapped totals. -/
@[stacks 015J "second-filtered Cartan-Eilenberg total map"]
noncomputable abbrev filteredTotal
    (f : Map I J) (F : A ⥤ B) [F.Additive] :
    HomologicalComplex₂.Second.Filtration.total (I.mapBicomplex F) ⟶
      HomologicalComplex₂.Second.Filtration.total (J.mapBicomplex F) :=
  HomologicalComplex₂.Second.Filtration.Map.hom (mapped f F)

/-- Forgetting the second filtration recovers the mapped total map. -/
@[simp]
theorem filteredTotal_underlying
    (f : Map I J) (F : A ⥤ B) [F.Additive] :
    FilteredComplex.underlyingMap (filteredTotal f F) = mappedTotal f F := sorry

/-- The second-filtered total construction preserves identity maps. -/
@[simp]
theorem filteredTotal_id (I : CartanEilenbergResolution K)
    (F : A ⥤ B) [F.Additive] :
    filteredTotal (id I) F = 𝟙 _ := sorry

/-- The second-filtered total construction preserves composition. -/
@[simp, reassoc]
theorem filteredTotal_comp (f : Map I J) (g : Map J N)
    (F : A ⥤ B) [F.Additive] :
    filteredTotal (comp f g) F = filteredTotal f F ≫ filteredTotal g F := sorry

end Second

end Mapped

end CochainComplex.CartanEilenbergResolution.Map
