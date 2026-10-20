module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap87.Definition_87_11_1_Representable
public import stacks_project.Chap87.Remark_87_2_3_McQuillan_s_variant_FormalScheme

/-!
# Functor of points of a McQuillan formal scheme on a chosen big fppf site

The fppf functor of points `h_X` of a McQuillan formal scheme on `(Sch/S)_fppf`
is the `ULift` of Hom-spaces from the comparison images of objects of the
chosen site.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

namespace AlgebraicGeometry.McQuillan.FormalScheme

/-- The points presheaf of a McQuillan formal scheme on a chosen big fppf site:
Hom-spaces `ofScheme.obj (𝒮.bigToScheme.obj T) ⟶ X`, lifted to
`Type (max u v)`. -/
def pointsPresheaf (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    (X : FormalScheme.{u}) :
    (𝒮.bigSite S)ᵒᵖ ⥤ Type (max u v) :=
  (𝒮.bigToScheme S).op ⋙ ofScheme.op ⋙ yoneda.obj X ⋙ uliftFunctor.{v}

/-- On objects, `pointsPresheaf` is the `ULift` of the Hom-type
`ofScheme.obj (𝒮.bigToScheme.obj T.unop) ⟶ X`. -/
theorem pointsPresheaf_obj (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    (X : FormalScheme.{u}) (T : (𝒮.bigSite S)ᵒᵖ) :
    (pointsPresheaf 𝒮 S X).obj T =
      ULift.{v} (ofScheme.obj ((𝒮.bigToScheme S).obj T.unop) ⟶ X) :=
  sorry

/-- The fppf functor of points of a McQuillan formal scheme on a chosen big
fppf site `(Sch/S)_fppf`. -/
def sheafOfPoints (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))] :
    FormalScheme.{u} ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)) where
  obj X :=
    { obj := pointsPresheaf 𝒮 S X
      property := sorry }
  map {X Y} f :=
    ObjectProperty.homMk
      (whiskerRight
        (whiskerLeft ((𝒮.bigToScheme S).op ⋙ ofScheme.op) (yoneda.map f))
        uliftFunctor.{v})
  map_id := sorry
  map_comp := sorry

/-- The underlying presheaf of `(sheafOfPoints 𝒮 S).obj X` is
`pointsPresheaf 𝒮 S X`. -/
theorem sheafOfPoints_val (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : FormalScheme.{u}) :
    ((sheafOfPoints 𝒮 S).obj X).obj = pointsPresheaf 𝒮 S X :=
  sorry

end AlgebraicGeometry.McQuillan.FormalScheme
