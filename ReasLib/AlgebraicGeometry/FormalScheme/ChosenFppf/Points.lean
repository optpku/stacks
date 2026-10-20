module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.FormalScheme.Scheme
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.ChosenPresentation

/-!
# Formal-scheme points on a chosen big fppf site

The lifted Hom presheaves of formal schemes form a sheaf-valued functor.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

namespace AlgebraicGeometry.FormalScheme

/-- The points presheaf of an EGA formal scheme on a chosen big fppf site:
Hom-spaces `toFormalScheme.obj (𝒮.bigToScheme.obj T) ⟶ X`, lifted to
`Type (max u v)`. -/
def pointsPresheaf (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    (X : FormalScheme.{u}) :
    (𝒮.bigSite S)ᵒᵖ ⥤ Type (max u v) :=
  (𝒮.bigToScheme S).op ⋙ Scheme.toFormalScheme.op ⋙ yoneda.obj X ⋙
    uliftFunctor.{v}

/-- On objects, `pointsPresheaf` is the `ULift` of the Hom-type
`toFormalScheme.obj (𝒮.bigToScheme.obj T.unop) ⟶ X`. -/
theorem pointsPresheaf_obj (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    (X : FormalScheme.{u}) (T : (𝒮.bigSite S)ᵒᵖ) :
    (pointsPresheaf 𝒮 S X).obj T =
      ULift.{v} (Scheme.toFormalScheme.obj ((𝒮.bigToScheme S).obj T.unop) ⟶ X) :=
  rfl

/-- The lifted Hom presheaf of a formal scheme satisfies fppf descent. -/
theorem pointsPresheaf_isSheaf (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : FormalScheme.{u}) :
    Presheaf.IsSheaf (𝒮.bigTopology S) (pointsPresheaf 𝒮 S X) :=
  sorry

/-- The fppf functor of points of an EGA formal scheme on a chosen big fppf
site `(Sch/S)_fppf`. -/
def sheafOfPoints (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))] :
    FormalScheme.{u} ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)) :=
  ObjectProperty.lift (Presheaf.IsSheaf (𝒮.bigTopology S))
    (yoneda ⋙
      (whiskeringLeft (𝒮.bigSite S)ᵒᵖ (FormalScheme.{u})ᵒᵖ (Type u)).obj
        ((𝒮.bigToScheme S).op ⋙ Scheme.toFormalScheme.op) ⋙
      (whiskeringRight (𝒮.bigSite S)ᵒᵖ (Type u) (Type (max u v))).obj
        uliftFunctor.{v})
    (pointsPresheaf_isSheaf 𝒮 S)

/-- The underlying presheaf of `(sheafOfPoints 𝒮 S).obj X` is
`pointsPresheaf 𝒮 S X`. -/
theorem sheafOfPoints_val (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : FormalScheme.{u}) :
    ((sheafOfPoints 𝒮 S).obj X).obj = pointsPresheaf 𝒮 S X :=
  rfl

end AlgebraicGeometry.FormalScheme
