/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Basic

/-!
# Components for sequential postcomposition of colax costructured arrows

For composable target `1`-morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, direct
postcomposition by `f ≫ g` and successive postcomposition by `f` and then `g`
have associator-related structural maps. This leaf owns the two explicit
colax costructured-arrow components between those objects. Their source maps
are identities; the structural comparisons use the map-identity comparison of
`K`, a left unitor, and the target associator.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe uA vA wA uC vC wC

namespace CategoryTheory

open Bicategory

namespace Bicategory.ColaxCostructuredArrow

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {K : Pseudofunctor A C}
variable {X Y Z : C}

/-- The forward component from direct to successive target postcomposition.

Its source map is `𝟙 S.left`; its normalized comparison removes `K.map (𝟙 _)`
and then applies the associator from `(S.hom ≫ f) ≫ g` to `S.hom ≫ (f ≫ g)`. -/
def postcompose.composition.component.hom
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    postcompose.obj (f ≫ g) S ⟶
      postcompose.obj g (postcompose.obj f S) :=
  ColaxCostructuredArrow.homMk (K := K) (X := Z)
    (𝟙 S.left)
    ((K.mapId S.left).hom ▷ ((S.hom ≫ f) ≫ g) ≫
      (λ_ ((S.hom ≫ f) ≫ g)).hom ≫
        (α_ S.hom f g).hom)

/-- The forward sequential-postcomposition component has identity source map. -/
@[simp]
theorem postcompose.composition.component.hom.map
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map (K := K) (X := Z)
        (postcompose.composition.component.hom f g S) =
      𝟙 S.left := sorry

/-- The normalized comparison of the forward sequential-postcomposition
component is its explicit map-identity, unitor, and associator pasting. -/
@[simp]
theorem postcompose.composition.component.hom.fac
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.fac (K := K) (X := Z)
        (postcompose.composition.component.hom f g S) =
      (K.mapId S.left).hom ▷ ((S.hom ≫ f) ≫ g) ≫
        (λ_ ((S.hom ≫ f) ≫ g)).hom ≫
          (α_ S.hom f g).hom := sorry

/-- The reverse component from successive to direct target postcomposition.

Its source map is `𝟙 S.left`; its normalized comparison uses the inverse
target associator after removing `K.map (𝟙 _)`. -/
def postcompose.composition.component.inv
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    postcompose.obj g (postcompose.obj f S) ⟶
      postcompose.obj (f ≫ g) S :=
  ColaxCostructuredArrow.homMk (K := K) (X := Z)
    (𝟙 S.left)
    ((K.mapId S.left).hom ▷ (S.hom ≫ (f ≫ g)) ≫
      (λ_ (S.hom ≫ (f ≫ g))).hom ≫
        (α_ S.hom f g).inv)

/-- The reverse sequential-postcomposition component has identity source map. -/
@[simp]
theorem postcompose.composition.component.inv.map
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map (K := K) (X := Z)
        (postcompose.composition.component.inv f g S) =
      𝟙 S.left := sorry

/-- The normalized comparison of the reverse sequential-postcomposition
component is its explicit map-identity, unitor, and inverse-associator
pasting. -/
@[simp]
theorem postcompose.composition.component.inv.fac
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.fac (K := K) (X := Z)
        (postcompose.composition.component.inv f g S) =
      (K.mapId S.left).hom ▷ (S.hom ≫ (f ≫ g)) ≫
        (λ_ (S.hom ≫ (f ≫ g))).hom ≫
          (α_ S.hom f g).inv := sorry

/- Data and axiom audit (mathlib 4.32):

Both components retain the literal source map `𝟙 S.left`. Their normalized
comparisons are explicit pastings of `K.mapId`, a left unitor, and the ambient
associator or its inverse. The accompanying readout theorems are
`Prop`-valued; no object, map, or comparison cell is selected by a proof
placeholder. -/

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
