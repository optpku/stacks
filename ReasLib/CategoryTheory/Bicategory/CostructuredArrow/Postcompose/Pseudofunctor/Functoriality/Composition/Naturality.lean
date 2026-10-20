module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Iso
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Functoriality.Composition.Component

/-!
# Strong naturality for sequential postcomposition

This leaf supplies the source-morphism naturality isomorphism for the
objectwise sequential-postcomposition component. The source-map comparison is
the standard right-unitor followed by inverse left-unitor; all target-specific
data remain in the explicit component maps.
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
variable {X Y Z : C}

namespace Implementation

/-- The source-map unitor comparison for sequential-postcomposition
naturality. -/
private def postcompose.composition.naturality.sourceIso
    (f : X ⟶ Y) (g : Y ⟶ Z)
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ColaxCostructuredArrow.map (K := K) (X := Z)
        (postcompose.map (f ≫ g) u ≫
          postcompose.composition.component.hom f g T) ≅
      ColaxCostructuredArrow.map (K := K) (X := Z)
        (postcompose.composition.component.hom f g S ≫
          postcompose.map g (postcompose.map f u)) :=
  ρ_ (ColaxCostructuredArrow.map (K := K) (X := X) u) ≪≫
    (λ_ (ColaxCostructuredArrow.map (K := K) (X := X) u)).symm

/-- Compatibility of the source-map unitor comparison with normalized
costructured-arrow comparisons. -/
private theorem postcompose.composition.naturality.comm
    (f : X ⟶ Y) (g : Y ⟶ Z)
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ((postcompose.obj g (postcompose.obj f T)).comparison S.left).map
          (postcompose.composition.naturality.sourceIso f g u).hom ≫
        ColaxCostructuredArrow.fac (K := K) (X := Z)
          (postcompose.composition.component.hom f g S ≫
            postcompose.map g (postcompose.map f u)) =
      ColaxCostructuredArrow.fac (K := K) (X := Z)
        (postcompose.map (f ≫ g) u ≫
          postcompose.composition.component.hom f g T) := sorry

end Implementation

/-- The strong naturality isomorphism from direct target postcomposition to
successive target postcomposition at a costructured-arrow morphism. -/
def postcompose.composition.naturality
    (f : X ⟶ Y) (g : Y ⟶ Z)
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    postcompose.map (f ≫ g) u ≫
        postcompose.composition.component.hom f g T ≅
      postcompose.composition.component.hom f g S ≫
        postcompose.map g (postcompose.map f u) :=
  ColaxCostructuredArrow.iso₂Mk
    (Implementation.postcompose.composition.naturality.sourceIso f g u)
    (Implementation.postcompose.composition.naturality.comm f g u)

/-- The forward source cell of sequential-postcomposition naturality is the
standard right-to-left unitor comparison. -/
@[simp]
theorem postcompose.composition.naturality.hom.map₂
    (f : X ⟶ Y) (g : Y ⟶ Z)
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Z)
        (postcompose.composition.naturality f g u).hom =
      (ρ_ (ColaxCostructuredArrow.map (K := K) (X := X) u) ≪≫
        (λ_ (ColaxCostructuredArrow.map
          (K := K) (X := X) u)).symm).hom := sorry

/-- The inverse source cell of sequential-postcomposition naturality is the
inverse standard unitor comparison. -/
@[simp]
theorem postcompose.composition.naturality.inv.map₂
    (f : X ⟶ Y) (g : Y ⟶ Z)
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Z)
        (postcompose.composition.naturality f g u).inv =
      (ρ_ (ColaxCostructuredArrow.map (K := K) (X := X) u) ≪≫
        (λ_ (ColaxCostructuredArrow.map
          (K := K) (X := X) u)).symm).inv := sorry

/- Data and axiom audit (mathlib 4.32):

`postcompose.composition.naturality` is lifted through
`ColaxCostructuredArrow.iso₂Mk` from the explicit right-unitor/inverse-left-
unitor source-map isomorphism. The only deferred datum is normalized-
comparison compatibility. -/

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
