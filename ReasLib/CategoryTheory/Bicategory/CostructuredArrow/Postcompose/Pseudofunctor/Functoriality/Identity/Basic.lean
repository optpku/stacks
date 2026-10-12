/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Functoriality.Identity.Naturality
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Functoriality.Identity.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Identity coherence for colax costructured-arrow postcomposition

This leaf compares postcomposition by an identity target `1`-morphism with the
identity pseudofunctor on the corresponding colax costructured-arrow
bicategory. It is an action-level comparison, not a declaration of strict
identity, because the structural maps differ by a target right unitor.
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
variable {X : C}

namespace Implementation

/-- Compatibility of identity-postcomposition naturality with source
`2`-morphisms. -/
private theorem postcompose.identity.impl.naturality.naturality
    (K : Pseudofunctor A C) (X : C) :
    ∀ {S T : ColaxCostructuredArrow K X} {u v : S ⟶ T} (η : u ⟶ v),
      (postcompose K (𝟙 X)).map₂ η ▷
          postcompose.identity.component.hom T ≫
        (postcompose.identity.naturality v).hom =
      (postcompose.identity.naturality u).hom ≫
        postcompose.identity.component.hom S ◁
          (Pseudofunctor.id (ColaxCostructuredArrow K X)).map₂ η := sorry

/-- Compatibility of identity-postcomposition naturality with source identity
morphisms. -/
private theorem postcompose.identity.impl.naturality.id
    (K : Pseudofunctor A C) (X : C) :
    ∀ S : ColaxCostructuredArrow K X,
      (postcompose.identity.naturality (𝟙 S)).hom ≫
          postcompose.identity.component.hom S ◁
            ((Pseudofunctor.id (ColaxCostructuredArrow K X)).mapId S).hom =
        ((postcompose K (𝟙 X)).mapId S).hom ▷
          postcompose.identity.component.hom S ≫
        (λ_ (postcompose.identity.component.hom S)).hom ≫
          (ρ_ (postcompose.identity.component.hom S)).inv := sorry

/-- Compatibility of identity-postcomposition naturality with source
composition. -/
private theorem postcompose.identity.impl.naturality.comp
    (K : Pseudofunctor A C) (X : C) :
    ∀ {R S T : ColaxCostructuredArrow K X} (u : R ⟶ S) (v : S ⟶ T),
      (postcompose.identity.naturality (u ≫ v)).hom ≫
          postcompose.identity.component.hom R ◁
            ((Pseudofunctor.id (ColaxCostructuredArrow K X)).mapComp u v).hom =
        ((postcompose K (𝟙 X)).mapComp u v).hom ▷
          postcompose.identity.component.hom T ≫
        (α_ _ _ _).hom ≫
          (postcompose K (𝟙 X)).map u ◁
            (postcompose.identity.naturality v).hom ≫
        (α_ _ _ _).inv ≫
          (postcompose.identity.naturality u).hom ▷
            (Pseudofunctor.id (ColaxCostructuredArrow K X)).map v ≫
          (α_ _ _ _).hom := sorry

end Implementation

/-- The strong transformation from postcomposition by `𝟙 X` to the identity
pseudofunctor on colax costructured arrows.

The defining pseudofunctor `K` and target object `X` are explicit: neither is
recoverable from the other, and together they determine the costructured-arrow
bicategory. -/
def postcompose.identity.strongTrans
    (K : Pseudofunctor A C) (X : C) :
    Pseudofunctor.StrongTrans
      (postcompose K (𝟙 X))
      (Pseudofunctor.id (ColaxCostructuredArrow K X)) where
  app S := postcompose.identity.component.hom S
  naturality u := postcompose.identity.naturality u
  naturality_naturality :=
    Implementation.postcompose.identity.impl.naturality.naturality K X
  naturality_id := Implementation.postcompose.identity.impl.naturality.id K X
  naturality_comp := Implementation.postcompose.identity.impl.naturality.comp K X

/-- The object component of identity-postcomposition coherence is the explicit
forward component. -/
@[simp]
theorem postcompose.identity.strongTrans.app
    {K : Pseudofunctor A C} {X : C} (S : ColaxCostructuredArrow K X) :
    (postcompose.identity.strongTrans K X).app S =
      postcompose.identity.component.hom S := sorry

/-- The strong naturality isomorphism of identity-postcomposition coherence is
the explicit costructured-arrow naturality isomorphism. -/
@[simp]
theorem postcompose.identity.strongTrans.naturality
    {K : Pseudofunctor A C} {X : C}
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    (postcompose.identity.strongTrans K X).naturality u =
      postcompose.identity.naturality u := sorry

/-- Pointwise equivalence data for identity-postcomposition coherence.

The target object is explicit because it cannot be recovered from `K`. -/
def postcompose.identity.pointwise
    (K : Pseudofunctor A C) (X : C) :
    Pseudofunctor.StrongTrans.PointwiseEquivalence
      (postcompose.identity.strongTrans K X) :=
  Pseudofunctor.StrongTrans.PointwiseEquivalence.ofComponents
    postcompose.identity.component.equivalence
    (fun _ ↦ Iso.refl _)

/-- Postcomposition by the explicit target identity `𝟙 X` is equivalent to the
identity pseudofunctor on colax costructured arrows. -/
def postcompose.identity.equivalence
    (K : Pseudofunctor A C) (X : C) :
    postcompose K (𝟙 X) ≌
      Pseudofunctor.id (ColaxCostructuredArrow K X) :=
  (postcompose.identity.pointwise K X).toEquivalence

/- Data and axiom audit (mathlib 4.32):

The strong transformation retains the explicit identity component and its
source-morphism naturality. Only the three `Prop`-valued
strong-transformation coherence fields are deferred. The pointwise
equivalence retains the explicit inverse supplied by
`postcompose.identity.component.equivalence`. -/

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
