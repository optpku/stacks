module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import ReasLib.AlgebraicGeometry.FormalScheme.Affine
public import ReasLib.AlgebraicGeometry.FormalScheme.ChosenFppf.Points
public import ReasLib.AlgebraicGeometry.FormalScheme.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.FormalSpectrum.QuotientDiagram
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypeConditions
public import ReasLib.AlgebraicGeometry.Scheme.SmallBoundClosed

/-!
# Affine formal schemes and classical affine sheaves

Over a terminal base, the chosen-fppf functor of points identifies bounded
affine formal schemes with classical affine formal algebraic spaces.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

namespace AlgebraicGeometry.FormalScheme

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
  rfl

/-- The diagram of functors of points of the affine stages `Spec(A ⧸ I)`, as
`I` runs over weak ideals of definition. -/
def ofSpfDiagram (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u}) :
    AffineFormalAlgebraicSpace.WeakIdealOfDefinition A ⥤
      Sheaf (𝒮.bigTopology S) (Type (max u v)) :=
  AffineFormalAlgebraicSpace.thickenings A (ofSpfStructureHom 𝒮 S hS A) ⋙
    Over.forget (𝒮.toScheme.obj S) ⋙ Scheme.toFormalScheme ⋙ sheafOfPoints 𝒮 S

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
  rfl

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
  rfl

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

/-- Over a terminal base, the points sheaf of an admissible formal spectrum
is a colimit of quotient-spectrum points sheaves indexed by ideals of definition. -/
theorem isColimit_ofSpfCocone (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u})
    (hA : TopologicalRing.IsAdmissibleRing A) :
    ∃ c : Cocone (ofSpfIdealOfDefinitionDiagram 𝒮 S hS A),
      Nonempty (IsColimit c) ∧
        Nonempty (c.pt ≅ (sheafOfPoints 𝒮 S).obj (ofSpf A hA)) :=
  sorry

/-- The points sheaf of an admissible formal spectrum is classical affine
on a small bound-closed chosen site that bounds its size. -/
theorem isClassicalAffine_sheafOfPoints_ofSpf
    (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsAdmissibleRing A)
    (hsize : ∃ T : 𝒮.carrier, (ofSpf A hA).size ≤ (𝒮.toScheme.obj T).size) :
    IsClassicalAffine ((sheafOfPoints 𝒮 S).obj (ofSpf A hA)) :=
  sorry

/-- The points functor is fully faithful on affine formal schemes when
the chosen site is small bound-closed and bounds the size of the source. -/
theorem sheafOfPoints_map_bijective (𝒮 : ChosenBigFppfSite.{u, v})
    (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    {X Y : FormalScheme.{u}} [IsAffine X] [IsAffine Y]
    (hX : ∃ T, X.size ≤ (𝒮.toScheme.obj T).size) :
    Function.Bijective
      ((sheafOfPoints 𝒮 S).map :
        (X ⟶ Y) → ((sheafOfPoints 𝒮 S).obj X ⟶ (sheafOfPoints 𝒮 S).obj Y)) :=
  sorry

/-- Over a terminal base, every classical affine sheaf is isomorphic
to the points sheaf of an affine formal scheme. -/
theorem exists_isAffine_iso_sheafOfPoints (𝒮 : ChosenBigFppfSite.{u, v})
    (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (F : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsClassicalAffine F] :
    ∃ (X : FormalScheme.{u}) (_ : IsAffine X),
      Nonempty ((sheafOfPoints 𝒮 S).obj X ≅ F) :=
  sorry

/-- The points sheaf of a bounded affine formal scheme is classical affine
on a small bound-closed chosen site over a terminal base. -/
theorem isClassicalAffine_sheafOfPoints
    (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    (X : FormalScheme.{u}) (hX : IsAffine X)
    (hsize : ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size) :
    IsClassicalAffine ((sheafOfPoints 𝒮 S).obj X) :=
  sorry

/-- Every classical affine sheaf on a small bound-closed chosen site over a
terminal base is the points sheaf of an affine formal scheme bounded by that site. -/
theorem exists_bounded_isAffine_iso_sheafOfPoints
    (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    (F : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsClassicalAffine F] :
    ∃ X : FormalScheme.{u}, IsAffine X ∧
      (∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size) ∧
      Nonempty ((sheafOfPoints 𝒮 S).obj X ≅ F) :=
  sorry

/-- The full subcategory of affine formal schemes whose size is bounded by
a represented scheme in the chosen site. -/
abbrev BoundedAffine (𝒮 : ChosenBigFppfSite.{u, v}) :=
  ObjectProperty.FullSubcategory (fun X : FormalScheme.{u} ↦
    IsAffine X ∧ ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size)

/-- The full subcategory of classical affine sheaves on a chosen big fppf slice. -/
abbrev ClassicalAffine (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))] :=
  ObjectProperty.FullSubcategory
    (fun F : Sheaf (𝒮.bigTopology S) (Type (max u v)) ↦ IsClassicalAffine F)

/-- The points functor restricted to bounded affine formal schemes and lifted
to classical affine sheaves on a small bound-closed chosen site over a terminal base. -/
def affineSheafOfPoints (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U))) :
    BoundedAffine 𝒮 ⥤ ClassicalAffine 𝒮 S :=
  ObjectProperty.lift
    (fun F : Sheaf (𝒮.bigTopology S) (Type (max u v)) ↦ IsClassicalAffine F)
    (ObjectProperty.ι (fun X : FormalScheme.{u} ↦
      IsAffine X ∧ ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size) ⋙
      sheafOfPoints 𝒮 S)
    (fun X ↦ isClassicalAffine_sheafOfPoints 𝒮 S hS h𝒮
      X.obj X.property.1 X.property.2)

/-- Over a terminal base, the points functor is an equivalence between bounded
affine formal schemes and classical affine sheaves on a small bound-closed site. -/
theorem affineSheafOfPoints_isEquivalence
    (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U))) :
    (affineSheafOfPoints 𝒮 S hS h𝒮).IsEquivalence :=
  sorry

end AlgebraicGeometry.FormalScheme
