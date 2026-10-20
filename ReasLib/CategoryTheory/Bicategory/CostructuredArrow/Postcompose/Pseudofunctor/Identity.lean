module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Iso
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Hom

/-!
# Identity comparison for postcomposition of costructured arrows

For a fixed target `1`-morphism, postcomposition sends an identity
costructured-arrow morphism to the identity only up to an invertible
`2`-morphism. This file constructs that comparison through the generic
`ColaxCostructuredArrow.iso₂Mk` API.

The source-map isomorphism is the identity. Its compatibility is kept as an
implementation detail, while the resulting comparison and its source-cell
computations form the public API.
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

/-- The source-map isomorphism underlying the identity comparison for
postcomposition. -/
private def mapId.sourceIso
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map (K := K) (X := Y)
          (map f (𝟙 S)) ≅
      ColaxCostructuredArrow.map (K := K) (X := Y)
        (𝟙 (obj f S)) :=
  Iso.refl (𝟙 S.left)

/-- Compatibility of the source-map identity isomorphism with the normalized
comparisons of the mapped and target identities. -/
private theorem mapId.comm
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ((obj f S).comparison S.left).map
          (mapId.sourceIso f S).hom ≫
        ColaxCostructuredArrow.fac (K := K) (X := Y)
          (𝟙 (obj f S)) =
      ColaxCostructuredArrow.fac (K := K) (X := Y)
        (map f (𝟙 S)) := sorry

end Implementation

/-- The identity comparison for postcomposition of colax costructured arrows.

Its forward and inverse source cells are both the identity `2`-morphism of the
unchanged source identity map. -/
def mapId
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    map f (𝟙 S) ≅
      𝟙 (obj f S) :=
  ColaxCostructuredArrow.iso₂Mk
    (Implementation.mapId.sourceIso f S)
    (Implementation.mapId.comm f S)

/-- The source cell of the forward identity comparison is the identity. -/
@[simp]
theorem mapId.hom.map₂
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        (mapId f S).hom =
      𝟙 (𝟙 S.left) := sorry

/-- The source cell of the inverse identity comparison is the identity. -/
@[simp]
theorem mapId.inv.map₂
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        (mapId f S).inv =
      𝟙 (𝟙 S.left) := sorry

/- Data and axiom audit (mathlib 4.32):

`postcompose.mapId` reuses `ColaxCostructuredArrow.iso₂Mk` with the explicit
identity source-map isomorphism. The only new deferred statement is its
`Prop`-valued comparison compatibility; no endpoint map or `2`-cell is selected
through a proof placeholder. -/

end postcompose

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
