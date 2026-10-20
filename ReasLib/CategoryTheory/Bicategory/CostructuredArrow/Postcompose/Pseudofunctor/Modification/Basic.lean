/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Modification.Naturality

/-!
# Strong transformations induced by target 2-morphisms

For a fixed pseudofunctor `K : A ⥤ᵖ C`, a target `2`-morphism
`η : f ⟶ g` induces a strong transformation

`postcompose K g ⟶ postcompose K f`.

The reversed direction is forced by the colax orientation of morphisms of
costructured arrows. Its object components are `postcompose.cellComponent η`,
and its strong naturality isomorphisms are `postcompose.cellNaturality η`.

This file performs only the `Pseudofunctor.StrongTrans` assembly. Identity and
vertical-composition functoriality of this construction belong in separate
modules.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uA vA wA uC vC wC

namespace CategoryTheory

open Bicategory

namespace Bicategory.ColaxCostructuredArrow

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {K : Pseudofunctor A C}
variable {X Y : C}

namespace postcompose

namespace Implementation

/-- Naturality of the strong comparison with respect to `2`-morphisms of
costructured arrows. -/
private theorem cellNaturality.naturality
    {f g : X ⟶ Y} (η : f ⟶ g)
    {S T : ColaxCostructuredArrow K X}
    {u v : S ⟶ T} (θ : u ⟶ v) :
    (postcompose K g).map₂ θ ▷
          cellComponent η T ≫
        (cellNaturality η v).hom =
      (cellNaturality η u).hom ≫
        cellComponent η S ◁
          (postcompose K f).map₂ θ := sorry

/-- Compatibility of target-cell naturality with the pseudofunctor identity
comparisons. -/
private theorem cellNaturality.id
    {f g : X ⟶ Y} (η : f ⟶ g)
    (S : ColaxCostructuredArrow K X) :
    (cellNaturality η (𝟙 S)).hom ≫
        cellComponent η S ◁
          ((postcompose K f).mapId S).hom =
      ((postcompose K g).mapId S).hom ▷
          cellComponent η S ≫
        (λ_ (cellComponent η S)).hom ≫
          (ρ_ (cellComponent η S)).inv := sorry

/-- Compatibility of target-cell naturality with the pseudofunctor
composition comparisons. -/
private theorem cellNaturality.comp
    {f g : X ⟶ Y} (η : f ⟶ g)
    {R S T : ColaxCostructuredArrow K X}
    (u : R ⟶ S) (v : S ⟶ T) :
    (cellNaturality η (u ≫ v)).hom ≫
        cellComponent η R ◁
          ((postcompose K f).mapComp u v).hom =
      ((postcompose K g).mapComp u v).hom ▷
          cellComponent η T ≫
        (α_ _ _ _).hom ≫
          (postcompose K g).map u ◁
            (cellNaturality η v).hom ≫
        (α_ _ _ _).inv ≫
          (cellNaturality η u).hom ▷
            (postcompose K f).map v ≫
        (α_ _ _ _).hom := sorry

end Implementation

/-- The contravariant strong transformation between costructured-arrow
postcomposition pseudofunctors induced by a target `2`-morphism.

For `η : f ⟶ g`, its direction is
`postcompose K g ⟶ postcompose K f`. -/
def cellStrongTrans
    (K : Pseudofunctor A C) {f g : X ⟶ Y} (η : f ⟶ g) :
    Pseudofunctor.StrongTrans
      (postcompose K g) (postcompose K f) where
  app := cellComponent η
  naturality := cellNaturality η
  naturality_naturality :=
    Implementation.cellNaturality.naturality η
  naturality_id := Implementation.cellNaturality.id η
  naturality_comp := Implementation.cellNaturality.comp η

/-- The object component of the target-cell strong transformation is the
corresponding contravariant costructured-arrow component. -/
@[simp]
theorem cellStrongTrans.app
    {f g : X ⟶ Y} (η : f ⟶ g)
    (S : ColaxCostructuredArrow K X) :
    (cellStrongTrans K η).app S =
      cellComponent η S := sorry

/-- The strong naturality isomorphism of the target-cell transformation is
the explicit costructured-arrow naturality isomorphism. -/
@[simp]
theorem cellStrongTrans.naturality
    {f g : X ⟶ Y} (η : f ⟶ g)
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    (cellStrongTrans K η).naturality u =
      cellNaturality η u := sorry

/- Data and axiom audit (mathlib 4.32):

`postcompose.cellStrongTrans` reuses the explicit component and naturality
owners from the preceding modules. Its three private helpers fill only
`Prop`-valued strong-transformation coherence fields; no component,
naturality isomorphism, source cell, or inverse is selected through a proof
placeholder. -/

end postcompose

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
