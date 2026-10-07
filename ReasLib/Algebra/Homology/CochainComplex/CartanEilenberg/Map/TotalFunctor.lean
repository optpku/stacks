module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Total

/-!
# Total-complex functors on Cartan--Eilenberg resolutions

Raw totals, bounded-below totals, mapped totals, and the two standard filtered totals are
assembled into functors on the category of bundled Cartan--Eilenberg resolutions.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex₂

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]

/-- Totalize the resolving double complex of a bundled Cartan--Eilenberg resolution. -/
@[stacks 015J "total functor of Cartan-Eilenberg resolutions"]
noncomputable def total : Bundled A ⥤ CochainComplex A ℤ where
  obj X := Total.complex X.resolution
  map f := Map.total f
  map_id X := Map.total_id X.resolution
  map_comp f g := Map.total_comp f g

/-- Totalize and retain the bounded-below structure of a bundled Cartan--Eilenberg
resolution. -/
@[stacks 015J "bounded-below total functor of Cartan-Eilenberg resolutions"]
noncomputable def totalPlus : Bundled A ⥤ CochainComplex.Plus A where
  obj X := Total.toPlus X.resolution
  map f := Map.totalPlus f
  map_id X := Map.totalPlus_id X.resolution
  map_comp f g := Map.totalPlus_comp f g

/-- The raw-total functor is computed by the total of the stored resolution. -/
@[simp, stacks 015J "total functor of Cartan-Eilenberg resolutions"]
theorem total_obj (X : Bundled A) :
    total.obj X = Total.complex X.resolution := sorry

/-- The raw-total functor is computed on maps by double-complex totalization. -/
@[simp, stacks 015J "total functor of Cartan-Eilenberg resolutions"]
theorem total_map {X Y : Bundled A} (f : X ⟶ Y) :
    (total : Bundled A ⥤ CochainComplex A ℤ).map f = Map.total f := sorry

/-- The bounded-total functor is computed by the bounded total of the stored resolution. -/
@[simp, stacks 015J "bounded-below total functor of Cartan-Eilenberg resolutions"]
theorem totalPlus_obj (X : Bundled A) :
    totalPlus.obj X = Total.toPlus X.resolution := sorry

/-- The bounded-total functor is computed on maps by the bounded total map. -/
@[simp, stacks 015J "bounded-below total functor of Cartan-Eilenberg resolutions"]
theorem totalPlus_map {X Y : Bundled A} (f : X ⟶ Y) :
    totalPlus.map f = Map.totalPlus f := sorry

section Mapped

variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- Totalize the resolving double complexes after applying an additive functor termwise. -/
@[stacks 015J "mapped total functor of Cartan-Eilenberg resolutions"]
noncomputable def mappedTotal (F : A ⥤ B) [F.Additive] :
    Bundled A ⥤ CochainComplex B ℤ where
  obj X := (X.resolution.mapBicomplex F).total (up ℤ)
  map f := Map.mappedTotal f F
  map_id X := Map.mappedTotal_id X.resolution F
  map_comp f g := Map.mappedTotal_comp f g F

/-- The mapped-total functor is computed by totalizing the termwise mapped resolution. -/
@[simp, stacks 015J "mapped total functor of Cartan-Eilenberg resolutions"]
theorem mappedTotal_obj (F : A ⥤ B) [F.Additive] (X : Bundled A) :
    (mappedTotal F).obj X = (X.resolution.mapBicomplex F).total (up ℤ) := sorry

/-- The mapped-total functor is computed on maps by mapped totalization. -/
@[simp, stacks 015J "mapped total functor of Cartan-Eilenberg resolutions"]
theorem mappedTotal_map (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} (f : X ⟶ Y) :
    (mappedTotal F).map f = Map.mappedTotal f F := sorry

namespace First

/-- The first standard filtration on mapped totals, functorial in a bundled
Cartan--Eilenberg resolution. -/
@[stacks 015J "first-filtered total functor of Cartan-Eilenberg resolutions"]
noncomputable def filteredTotal (F : A ⥤ B) [F.Additive] :
    Bundled A ⥤ FilteredComplex B where
  obj X := HomologicalComplex₂.First.Filtration.total (X.resolution.mapBicomplex F)
  map f := Map.First.filteredTotal f F
  map_id X := Map.First.filteredTotal_id X.resolution F
  map_comp f g := Map.First.filteredTotal_comp f g F

/-- The first-filtered-total functor is computed by the first filtration on the mapped
resolution total. -/
@[simp, stacks 015J "first-filtered total functor of Cartan-Eilenberg resolutions"]
theorem filteredTotal_obj (F : A ⥤ B) [F.Additive] (X : Bundled A) :
    (filteredTotal F).obj X =
      HomologicalComplex₂.First.Filtration.total (X.resolution.mapBicomplex F) := sorry

/-- The first-filtered-total functor is computed on maps by the first filtered total map. -/
@[simp, stacks 015J "first-filtered total functor of Cartan-Eilenberg resolutions"]
theorem filteredTotal_map (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} (f : X ⟶ Y) :
    (filteredTotal F).map f = Map.First.filteredTotal f F := sorry

/-- Forgetting the first filtration recovers the mapped-total functor. -/
@[simp, stacks 015J "underlying first-filtered total functor of Cartan-Eilenberg resolutions"]
theorem filteredTotal_forget (F : A ⥤ B) [F.Additive] :
    filteredTotal F ⋙ FilteredComplex.underlyingFunctor = mappedTotal F := sorry

end First

namespace Second

/-- The second standard filtration on mapped totals, functorial in a bundled
Cartan--Eilenberg resolution. -/
@[stacks 015J "second-filtered total functor of Cartan-Eilenberg resolutions"]
noncomputable def filteredTotal (F : A ⥤ B) [F.Additive] :
    Bundled A ⥤ FilteredComplex B where
  obj X := HomologicalComplex₂.Second.Filtration.total (X.resolution.mapBicomplex F)
  map f := Map.Second.filteredTotal f F
  map_id X := Map.Second.filteredTotal_id X.resolution F
  map_comp f g := Map.Second.filteredTotal_comp f g F

/-- The second-filtered-total functor is computed by the second filtration on the mapped
resolution total. -/
@[simp, stacks 015J "second-filtered total functor of Cartan-Eilenberg resolutions"]
theorem filteredTotal_obj (F : A ⥤ B) [F.Additive] (X : Bundled A) :
    (filteredTotal F).obj X =
      HomologicalComplex₂.Second.Filtration.total (X.resolution.mapBicomplex F) := sorry

/-- The second-filtered-total functor is computed on maps by the second filtered total map. -/
@[simp, stacks 015J "second-filtered total functor of Cartan-Eilenberg resolutions"]
theorem filteredTotal_map (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} (f : X ⟶ Y) :
    (filteredTotal F).map f = Map.Second.filteredTotal f F := sorry

/-- Forgetting the second filtration recovers the mapped-total functor. -/
@[simp, stacks 015J "underlying second-filtered total functor of Cartan-Eilenberg resolutions"]
theorem filteredTotal_forget (F : A ⥤ B) [F.Additive] :
    filteredTotal F ⋙ FilteredComplex.underlyingFunctor = mappedTotal F := sorry

end Second

end Mapped

end CochainComplex.CartanEilenbergResolution.Bundled
