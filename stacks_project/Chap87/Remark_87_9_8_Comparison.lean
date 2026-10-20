module

public import ReasLib.AlgebraicGeometry.FormalScheme.ChosenFppf.Points
public import ReasLib.AlgebraicGeometry.FormalScheme.ChosenFppf.Affine
public import stacks_project.Chap87.Definition_87_9_9_Spf
public import stacks_project.Chap87.Remark_87_9_8_Affine
import StacksCheckRecall

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

/- Remark 87.9.8. The chosen-fppf points presheaf and affine comparison. -/
@[stacks 0AIE] #check (AlgebraicGeometry.FormalScheme.pointsPresheaf :
    ∀ (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    (X : FormalScheme.{u}),
    (𝒮.bigSite S)ᵒᵖ ⥤ Type (max u v))

#check (AlgebraicGeometry.FormalScheme.pointsPresheaf_obj :
    ∀ (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    (X : FormalScheme.{u}) (T : (𝒮.bigSite S)ᵒᵖ),
    (pointsPresheaf 𝒮 S X).obj T =
      ULift.{v} (Scheme.toFormalScheme.obj ((𝒮.bigToScheme S).obj T.unop) ⟶ X))

#check (AlgebraicGeometry.FormalScheme.sheafOfPoints :
    ∀ (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))],
    FormalScheme.{u} ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)))

#check (AlgebraicGeometry.FormalScheme.sheafOfPoints_val :
    ∀ (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : FormalScheme.{u}),
    ((sheafOfPoints 𝒮 S).obj X).obj = pointsPresheaf 𝒮 S X)

#check (AlgebraicGeometry.FormalScheme.ofSpfStructureHom :
    ∀ (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u}),
    Spec (.of (A : Type u)) ⟶ 𝒮.toScheme.obj S)

#check (AlgebraicGeometry.FormalScheme.ofSpfStructureHom_eq :
    ∀ (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u}),
    ofSpfStructureHom 𝒮 S hS A = hS.from (Spec (.of (A : Type u))))

#check (AlgebraicGeometry.FormalScheme.ofSpfDiagram :
    ∀ (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u}),
    AffineFormalAlgebraicSpace.WeakIdealOfDefinition A ⥤
      Sheaf (𝒮.bigTopology S) (Type (max u v)))

#check (AlgebraicGeometry.FormalScheme.ofSpfDiagram_obj :
    ∀ (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u})
    (I : AffineFormalAlgebraicSpace.WeakIdealOfDefinition A),
    (ofSpfDiagram 𝒮 S hS A).obj I =
      (sheafOfPoints 𝒮 S).obj
        (Scheme.toFormalScheme.obj
          (AffineFormalAlgebraicSpace.stage A
            (ofSpfStructureHom 𝒮 S hS A) I).left))

#check (AlgebraicGeometry.FormalScheme.ofSpfIdealOfDefinitionDiagram :
    ∀ (𝒮 : ChosenBigFppfSite.{u, v})
    (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u}),
    ObjectProperty.FullSubcategory
        (fun I : AffineFormalAlgebraicSpace.WeakIdealOfDefinition A ↦
          TopologicalRing.Ideal.IsIdealOfDefinition I.ideal) ⥤
      Sheaf (𝒮.bigTopology S) (Type (max u v)))

#check (AlgebraicGeometry.FormalScheme.ofSpfIdealOfDefinitionDiagram_eq :
    ∀ (𝒮 : ChosenBigFppfSite.{u, v})
    (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u}),
    ofSpfIdealOfDefinitionDiagram 𝒮 S hS A =
      ObjectProperty.ι
          (fun I : AffineFormalAlgebraicSpace.WeakIdealOfDefinition A ↦
            TopologicalRing.Ideal.IsIdealOfDefinition I.ideal) ⋙
        ofSpfDiagram 𝒮 S hS A)

#check (AlgebraicGeometry.FormalScheme.sheafOfPoints_iso_spf :
    ∀ (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u})
    (hA : TopologicalRing.IsAdmissibleRing A),
    ∃ c : Cocone (ofSpfDiagram 𝒮 S hS A),
      Nonempty (IsColimit c) ∧
        Nonempty (c.pt ≅ (sheafOfPoints 𝒮 S).obj (ofSpf A hA)))

end AlgebraicGeometry.FormalScheme
