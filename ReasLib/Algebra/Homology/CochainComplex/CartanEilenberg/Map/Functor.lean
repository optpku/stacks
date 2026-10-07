module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Functoriality
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Category
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Views

/-!
# Applying a functor to a map of Cartan--Eilenberg resolutions

This leaf exposes the single mapped double-complex morphism reused by total and initial-page
constructions.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B]
variable {K L M : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}
variable {N : CartanEilenbergResolution M}

/-- The double-complex map obtained by applying an additive functor termwise. -/
@[stacks 015J "mapped Cartan-Eilenberg resolution map"]
noncomputable abbrev mapped (f : Map I J) (F : A ⥤ B) [F.Additive] :
    I.mapBicomplex F ⟶ J.mapBicomplex F :=
  (F.mapHomologicalComplex₂ (up ℤ) (up ℤ)).map f.hom

/-- The row map obtained after applying an additive functor termwise. -/
@[stacks 015J "mapped row of a Cartan-Eilenberg resolution map"]
noncomputable abbrev mappedRow
    (f : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    (I.mapBicomplex F).flip.X q ⟶ (J.mapBicomplex F).flip.X q :=
  ((HomologicalComplex₂.flipFunctor B (up ℤ) (up ℤ)).map (mapped f F)).f q

/-- Mapping the identity resolution map gives the identity mapped double-complex map. -/
@[simp]
theorem mapped_id (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive] :
    mapped (id I) F = 𝟙 (I.mapBicomplex F) := sorry

/-- Mapping a composite resolution map gives the composite mapped double-complex map. -/
@[simp, reassoc]
theorem mapped_comp (f : Map I J) (g : Map J N) (F : A ⥤ B) [F.Additive] :
    mapped (comp f g) F = mapped f F ≫ mapped g F := sorry

/-- The mapped double-complex map in horizontal degree `p` is obtained by applying the mapped
cochain-complex functor to the corresponding column map. -/
@[simp]
theorem mapped_f (f : Map I J) (F : A ⥤ B) [F.Additive] (p : ℤ) :
    (mapped f F).f p = (F.mapHomologicalComplex (up ℤ)).map (column f p) := sorry

/-- The bidegree component of the mapped double-complex map is the functorial image of the
original bidegree component. -/
@[simp]
theorem mapped_f_f (f : Map I J) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    ((mapped f F).f p).f q = F.map (term f p q) := sorry

/-- A mapped row is obtained by applying the mapped-complex functor to the original row map. -/
@[simp, stacks 015J "mapped row of a Cartan-Eilenberg resolution map"]
theorem mappedRow_eq (f : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    mappedRow f F q = (F.mapHomologicalComplex (up ℤ)).map (row f q) := sorry

/-- Mapping an identity resolution map gives the identity on every mapped row. -/
@[simp]
theorem mappedRow_id (I : CartanEilenbergResolution K)
    (F : A ⥤ B) [F.Additive] (q : ℤ) :
    mappedRow (id I) F q = 𝟙 _ := sorry

/-- Mapping a composite resolution map gives the composite on every mapped row. -/
@[simp, reassoc]
theorem mappedRow_comp (f : Map I J) (g : Map J N)
    (F : A ⥤ B) [F.Additive] (q : ℤ) :
    mappedRow (comp f g) F q = mappedRow f F q ≫ mappedRow g F q := sorry

end CochainComplex.CartanEilenbergResolution.Map

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B]

/-- Apply an additive functor termwise to the resolving double complex of every bundled
Cartan--Eilenberg resolution. -/
@[stacks 015J "mapped double-complex functor of Cartan-Eilenberg resolutions"]
noncomputable def mapBicomplex (F : A ⥤ B) [F.Additive] :
    Bundled A ⥤ HomologicalComplex₂ B (up ℤ) (up ℤ) where
  obj X := X.resolution.mapBicomplex F
  map f := Map.mapped f F
  map_id X := Map.mapped_id X.resolution F
  map_comp f g := Map.mapped_comp f g F

/-- The mapped-double-complex functor is computed objectwise by termwise application. -/
@[simp, stacks 015J "mapped double-complex functor of Cartan-Eilenberg resolutions"]
theorem mapBicomplex_obj (F : A ⥤ B) [F.Additive] (X : Bundled A) :
    (mapBicomplex F).obj X = X.resolution.mapBicomplex F := sorry

/-- The mapped-double-complex functor sends a resolution morphism to its termwise image. -/
@[simp, stacks 015J "mapped double-complex functor of Cartan-Eilenberg resolutions"]
theorem mapBicomplex_map (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} (f : X ⟶ Y) :
    (mapBicomplex F).map f = Map.mapped f F := sorry

end CochainComplex.CartanEilenbergResolution.Bundled
