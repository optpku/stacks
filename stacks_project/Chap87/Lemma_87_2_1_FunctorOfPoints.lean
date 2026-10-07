module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap87.«87_2_0_2_FormalScheme»

/-!
# Functor of points of a formal scheme

The functor of points of a formal scheme, restricted to a full subcategory of
schemes, is the Yoneda embedding whiskered along the comparison functor
`Scheme.toFormalScheme`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.FormalScheme

/-- The functor of points of formal schemes, restricted to the full subcategory
selected by an object property `P` of schemes: `h_X(S)` is the type of morphisms
of formal schemes from the comparison image of `S` to `X`. -/
def functorOfPoints (P : ObjectProperty Scheme.{u}) :
    FormalScheme.{u} ⥤ (P.FullSubcategory)ᵒᵖ ⥤ Type u :=
  yoneda ⋙ (Functor.whiskeringLeft (P.FullSubcategory)ᵒᵖ (FormalScheme.{u})ᵒᵖ (Type u)).obj
    (P.ι ⋙ Scheme.toFormalScheme).op

/-- On objects, the restricted functor of points is the Hom-type
`toFormalScheme.obj (P.ι.obj S.unop) ⟶ X`. -/
theorem functorOfPoints_obj (P : ObjectProperty Scheme.{u}) (X : FormalScheme.{u})
    (S : (P.FullSubcategory)ᵒᵖ) :
    ((functorOfPoints P).obj X).obj S =
      (Scheme.toFormalScheme.obj (P.ι.obj S.unop) ⟶ X) :=
  sorry

end AlgebraicGeometry.FormalScheme
