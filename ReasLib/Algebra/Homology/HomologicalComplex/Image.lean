module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Images of differentials in homological complexes

This file packages the map on differential images induced by a morphism of homological complexes.
It supplies the two defining computations, identity and composition laws, and the resulting
image functor at a fixed pair of degrees.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {c : ComplexShape ι}
variable {K L M : HomologicalComplex C c}

/-- The map on images of the `(i, j)`-differential induced by a morphism of complexes. -/
noncomputable def imageMap (φ : K ⟶ L) (i j : ι) :
    image (K.d i j) ⟶ image (L.d i j) :=
  image.map (Arrow.homMk' (φ.f i) (φ.f j) (φ.comm i j))

/-- Factoring a differential through its image is natural in the complex. -/
@[reassoc (attr := simp)]
theorem factorThruImage_imageMap (φ : K ⟶ L) (i j : ι) :
    factorThruImage (K.d i j) ≫ imageMap φ i j =
      φ.f i ≫ factorThruImage (L.d i j) := sorry

/-- The inclusion of a differential image is natural in the complex. -/
@[reassoc (attr := simp)]
theorem imageMap_image_ι (φ : K ⟶ L) (i j : ι) :
    imageMap φ i j ≫ image.ι (L.d i j) = image.ι (K.d i j) ≫ φ.f j := sorry

/-- The map on differential images induced by the identity is the identity. -/
@[simp]
theorem imageMap_id (K : HomologicalComplex C c) (i j : ι) :
    imageMap (𝟙 K) i j = 𝟙 (image (K.d i j)) := sorry

/-- Maps on differential images respect composition of complex morphisms. -/
@[reassoc (attr := simp)]
theorem imageMap_comp (φ : K ⟶ L) (ψ : L ⟶ M) (i j : ι) :
    imageMap (φ ≫ ψ) i j = imageMap φ i j ≫ imageMap ψ i j := sorry

/-- At fixed degrees, taking the image of the differential is functorial in the complex. -/
noncomputable def imageFunctor (i j : ι) : HomologicalComplex C c ⥤ C where
  obj K := image (K.d i j)
  map φ := imageMap φ i j
  map_id K := imageMap_id K i j
  map_comp φ ψ := imageMap_comp φ ψ i j

/-- The image functor sends a complex to the image of its selected differential. -/
@[simp]
theorem imageFunctor_obj (i j : ι) (K : HomologicalComplex C c) :
    (imageFunctor i j).obj K = image (K.d i j) := sorry

/-- The image functor sends a complex morphism to its canonical map on differential images. -/
@[simp]
theorem imageFunctor_map (i j : ι) (φ : K ⟶ L) :
    (imageFunctor i j).map φ = imageMap φ i j := sorry

end HomologicalComplex
