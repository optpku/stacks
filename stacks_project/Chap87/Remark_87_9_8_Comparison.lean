module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap87.Definition_87_9_9_Spf
public import stacks_project.Chap87.Remark_87_9_8_Affine

/-!
# Functor of points of an EGA formal scheme on a chosen big fppf site

The fppf functor of points of an EGA formal scheme on `(Sch/S)_fppf` is the
`ULift` of Hom-spaces from the comparison images of objects of the chosen
site.
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
  sorry

/-- The fppf functor of points of an EGA formal scheme on a chosen big fppf
site `(Sch/S)_fppf`. -/
def sheafOfPoints (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))] :
    FormalScheme.{u} ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)) where
  obj X :=
    { obj := pointsPresheaf 𝒮 S X
      property := sorry }
  map {X Y} f :=
    ObjectProperty.homMk
      (whiskerRight
        (whiskerLeft ((𝒮.bigToScheme S).op ⋙ Scheme.toFormalScheme.op)
          (yoneda.map f))
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

/-- The unique structure morphism `Spec A ⟶ 𝒮.toScheme.obj S` supplied by
terminality of the base. -/
def ofSpfStructureHom (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u}) :
    Spec (.of (A : Type u)) ⟶ 𝒮.toScheme.obj S :=
  hS.from (Spec (.of (A : Type u)))

/-- `ofSpfStructureHom` is the unique morphism from `Spec A` to the terminal
base. -/
theorem ofSpfStructureHom_eq (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u}) :
    ofSpfStructureHom 𝒮 S hS A = hS.from (Spec (.of (A : Type u))) :=
  sorry

/-- The diagram of functors of points of the affine stages `Spec(A ⧸ I)`, as
`I` runs over weak ideals of definition. -/
def ofSpfDiagram (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u}) :
    AffineFormalAlgebraicSpace.WeakIdealOfDefinition A ⥤
      Sheaf (𝒮.bigTopology S) (Type (max u v)) where
  obj I :=
    (sheafOfPoints 𝒮 S).obj
      (Scheme.toFormalScheme.obj
        (AffineFormalAlgebraicSpace.stage A (ofSpfStructureHom 𝒮 S hS A) I).left)
  map {I J} f :=
    (sheafOfPoints 𝒮 S).map
      (Scheme.toFormalScheme.map
        ((AffineFormalAlgebraicSpace.thickenings A
            (ofSpfStructureHom 𝒮 S hS A)).map f).left)
  map_id := sorry
  map_comp := sorry

/-- Objects of `ofSpfDiagram` are the functors of points of the stages
`Spec(A ⧸ I)`. -/
theorem ofSpfDiagram_obj (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u})
    (I : AffineFormalAlgebraicSpace.WeakIdealOfDefinition A) :
    (ofSpfDiagram 𝒮 S hS A).obj I =
      (sheafOfPoints 𝒮 S).obj
        (Scheme.toFormalScheme.obj
          (AffineFormalAlgebraicSpace.stage A
            (ofSpfStructureHom 𝒮 S hS A) I).left) :=
  sorry

/-- The subdiagram of `ofSpfDiagram` indexed by ideals of definition of an
admissible ring. -/
def ofSpfIdealOfDefinitionDiagram (𝒮 : ChosenBigFppfSite.{u, v})
    (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u}) :
    ObjectProperty.FullSubcategory
        (fun I : AffineFormalAlgebraicSpace.WeakIdealOfDefinition A ↦
          TopologicalRing.Ideal.IsIdealOfDefinition I.ideal) ⥤
      Sheaf (𝒮.bigTopology S) (Type (max u v)) :=
  ObjectProperty.ι
      (fun I : AffineFormalAlgebraicSpace.WeakIdealOfDefinition A ↦
        TopologicalRing.Ideal.IsIdealOfDefinition I.ideal) ⋙
    ofSpfDiagram 𝒮 S hS A

/-- `ofSpfIdealOfDefinitionDiagram` is the inclusion of ideals of definition
followed by `ofSpfDiagram`. -/
theorem ofSpfIdealOfDefinitionDiagram_eq (𝒮 : ChosenBigFppfSite.{u, v})
    (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u}) :
    ofSpfIdealOfDefinitionDiagram 𝒮 S hS A =
      ObjectProperty.ι
          (fun I : AffineFormalAlgebraicSpace.WeakIdealOfDefinition A ↦
            TopologicalRing.Ideal.IsIdealOfDefinition I.ideal) ⋙
        ofSpfDiagram 𝒮 S hS A :=
  sorry

/-- Over a terminal base, the functor of points of `ofSpf A` is a colimit of
the functors of points of the affine stages `Spec(A ⧸ I)`, as `I` runs over
weak ideals of definition. -/
theorem sheafOfPoints_iso_spf (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u})
    (hA : TopologicalRing.IsAdmissibleRing A) :
    ∃ c : Cocone (ofSpfDiagram 𝒮 S hS A),
      Nonempty (IsColimit c) ∧
        Nonempty (c.pt ≅ (sheafOfPoints 𝒮 S).obj (ofSpf A hA)) :=
  sorry

end AlgebraicGeometry.FormalScheme

