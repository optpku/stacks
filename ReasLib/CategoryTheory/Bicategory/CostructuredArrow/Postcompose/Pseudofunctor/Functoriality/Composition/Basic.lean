module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Functoriality.Composition.Naturality
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Functoriality.Composition.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Composition coherence for colax costructured-arrow postcomposition

For composable target `1`-morphisms, this leaf compares direct
postcomposition by their composite with successive postcomposition. It does
not claim a global target pseudofunctor: local target `2`-cells act
contravariantly on colax costructured arrows, while this is only the coherent
composition comparison for a composable pair of target `1`-morphisms.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe uA vA wA uC vC wC

namespace CategoryTheory

open Bicategory

namespace Bicategory.ColaxCostructuredArrow

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {X Y Z : C}

namespace Implementation

/-- Compatibility of sequential-postcomposition naturality with source
`2`-morphisms. -/
private theorem postcompose.composition.impl.naturality.naturality
    (K : Pseudofunctor A C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ {S T : ColaxCostructuredArrow K X} {u v : S ⟶ T} (η : u ⟶ v),
      (postcompose K (f ≫ g)).map₂ η ▷
          postcompose.composition.component.hom f g T ≫
        (postcompose.composition.naturality f g v).hom =
      (postcompose.composition.naturality f g u).hom ≫
        postcompose.composition.component.hom f g S ◁
          ((postcompose K f).comp (postcompose K g)).map₂ η := sorry

/-- Compatibility of sequential-postcomposition naturality with source
identity morphisms. -/
private theorem postcompose.composition.impl.naturality.id
    (K : Pseudofunctor A C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ S : ColaxCostructuredArrow K X,
      (postcompose.composition.naturality f g (𝟙 S)).hom ≫
          postcompose.composition.component.hom f g S ◁
            (((postcompose K f).comp (postcompose K g)).mapId S).hom =
        ((postcompose K (f ≫ g)).mapId S).hom ▷
          postcompose.composition.component.hom f g S ≫
        (λ_ (postcompose.composition.component.hom f g S)).hom ≫
          (ρ_ (postcompose.composition.component.hom f g S)).inv := sorry

/-- Compatibility of sequential-postcomposition naturality with source
composition. -/
private theorem postcompose.composition.impl.naturality.comp
    (K : Pseudofunctor A C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ {R S T : ColaxCostructuredArrow K X} (u : R ⟶ S) (v : S ⟶ T),
      (postcompose.composition.naturality f g (u ≫ v)).hom ≫
          postcompose.composition.component.hom f g R ◁
            (((postcompose K f).comp (postcompose K g)).mapComp u v).hom =
        ((postcompose K (f ≫ g)).mapComp u v).hom ▷
          postcompose.composition.component.hom f g T ≫
        (α_ _ _ _).hom ≫
          (postcompose K (f ≫ g)).map u ◁
            (postcompose.composition.naturality f g v).hom ≫
        (α_ _ _ _).inv ≫
          (postcompose.composition.naturality f g u).hom ▷
            ((postcompose K f).comp (postcompose K g)).map v ≫
          (α_ _ _ _).hom := sorry

end Implementation

/-- The strong transformation from direct postcomposition by `f ≫ g` to
successive postcomposition by `f` and then `g`.

The defining pseudofunctor `K` is explicit because the target maps do not
determine the source bicategory or the costructured-arrow bicategories. -/
def postcompose.composition.strongTrans
    (K : Pseudofunctor A C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    Pseudofunctor.StrongTrans
      (postcompose K (f ≫ g))
      ((postcompose K f).comp (postcompose K g)) where
  app S := postcompose.composition.component.hom f g S
  naturality u := postcompose.composition.naturality f g u
  naturality_naturality :=
    Implementation.postcompose.composition.impl.naturality.naturality K f g
  naturality_id := Implementation.postcompose.composition.impl.naturality.id K f g
  naturality_comp := Implementation.postcompose.composition.impl.naturality.comp K f g

/-- The object component of sequential-postcomposition coherence is the
explicit forward component. -/
@[simp]
theorem postcompose.composition.strongTrans.app
    {K : Pseudofunctor A C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (S : ColaxCostructuredArrow K X) :
    (postcompose.composition.strongTrans K f g).app S =
      postcompose.composition.component.hom f g S := sorry

/-- The strong naturality isomorphism of sequential-postcomposition coherence
is the explicit costructured-arrow naturality isomorphism. -/
@[simp]
theorem postcompose.composition.strongTrans.naturality
    {K : Pseudofunctor A C} (f : X ⟶ Y) (g : Y ⟶ Z)
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    (postcompose.composition.strongTrans K f g).naturality u =
      postcompose.composition.naturality f g u := sorry

/-- Pointwise equivalence data for sequential-postcomposition coherence. -/
def postcompose.composition.pointwise
    (K : Pseudofunctor A C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    Pseudofunctor.StrongTrans.PointwiseEquivalence
      (postcompose.composition.strongTrans K f g) :=
  Pseudofunctor.StrongTrans.PointwiseEquivalence.ofComponents
    (fun S => postcompose.composition.component.equivalence f g S)
    (fun _ ↦ Iso.refl _)

/-- Direct postcomposition by a composite target `1`-morphism is equivalent
to successive postcomposition.

The equivalence is oriented from `postcompose K (f ≫ g)` to
`(postcompose K f).comp (postcompose K g)`, allowing downstream constructions
to retain a direct target action until a chosen factorization is needed. -/
def postcompose.composition.equivalence
    (K : Pseudofunctor A C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    postcompose K (f ≫ g) ≌
      (postcompose K f).comp (postcompose K g) :=
  (postcompose.composition.pointwise K f g).toEquivalence

/- Data and axiom audit (mathlib 4.32):

The strong transformation retains the explicit component and naturality data
from the preceding leaves. Its private helpers fill only the three
`Prop`-valued strong-transformation coherence fields. The pointwise
equivalence retains the explicit objectwise inverse from
`postcompose.composition.component.equivalence`; no source map, comparison cell, or inverse
is chosen by a proof placeholder. -/

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
