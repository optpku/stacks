module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Iso
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Functoriality.Identity.Component

/-!
# Strong naturality for identity postcomposition

This leaf supplies the source-morphism naturality isomorphism for the
identity-postcomposition component. Its source-map comparison is the standard
right-unitor followed by inverse left-unitor.
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
variable {X : C}

namespace Implementation

/-- The source-map unitor comparison for identity-postcomposition naturality. -/
private def postcompose.identity.naturality.sourceIso
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ColaxCostructuredArrow.map (K := K) (X := X)
        (postcompose.map (𝟙 X) u ≫
          postcompose.identity.component.hom T) ≅
      ColaxCostructuredArrow.map (K := K) (X := X)
        (postcompose.identity.component.hom S ≫ u) :=
  ρ_ (ColaxCostructuredArrow.map (K := K) (X := X) u) ≪≫
    (λ_ (ColaxCostructuredArrow.map (K := K) (X := X) u)).symm

/-- Compatibility of the identity-postcomposition source-map unitor
comparison with normalized costructured-arrow comparisons. -/
private theorem postcompose.identity.naturality.comm
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    (T.comparison S.left).map
          (postcompose.identity.naturality.sourceIso u).hom ≫
        ColaxCostructuredArrow.fac (K := K) (X := X)
          (postcompose.identity.component.hom S ≫ u) =
      ColaxCostructuredArrow.fac (K := K) (X := X)
        (postcompose.map (𝟙 X) u ≫
          postcompose.identity.component.hom T) := sorry

end Implementation

/-- The strong naturality isomorphism from postcomposition by `𝟙 X` to the
identity action at a costructured-arrow morphism. -/
def postcompose.identity.naturality
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    postcompose.map (𝟙 X) u ≫
        postcompose.identity.component.hom T ≅
      postcompose.identity.component.hom S ≫ u :=
  ColaxCostructuredArrow.iso₂Mk
    (Implementation.postcompose.identity.naturality.sourceIso u)
    (Implementation.postcompose.identity.naturality.comm u)

/-- The forward source cell of identity-postcomposition naturality is the
standard right-to-left unitor comparison. -/
@[simp]
theorem postcompose.identity.naturality.hom.map₂
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ColaxCostructuredArrow.map₂ (K := K) (X := X)
        (postcompose.identity.naturality u).hom =
      (ρ_ (ColaxCostructuredArrow.map (K := K) (X := X) u) ≪≫
        (λ_ (ColaxCostructuredArrow.map
          (K := K) (X := X) u)).symm).hom := sorry

/-- The inverse source cell of identity-postcomposition naturality is the
inverse standard unitor comparison. -/
@[simp]
theorem postcompose.identity.naturality.inv.map₂
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ColaxCostructuredArrow.map₂ (K := K) (X := X)
        (postcompose.identity.naturality u).inv =
      (ρ_ (ColaxCostructuredArrow.map (K := K) (X := X) u) ≪≫
        (λ_ (ColaxCostructuredArrow.map
          (K := K) (X := X) u)).symm).inv := sorry

/- Data and axiom audit (mathlib 4.32):

`postcompose.identity.naturality` is the `iso₂Mk` lift of an explicit
right-unitor/inverse-left-unitor source-map isomorphism. Only its normalized
comparison compatibility is proof debt. -/

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
