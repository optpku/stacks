module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Hom.Construction

/-!
# Identity coherence for changing cospan

This module records the identity comparison for the action of a walking-cospan transformation
on readable pseudopullback-cone morphisms.  Its component is literally the identity cell at the
apex; the remaining coherence is carried by the cone comparison modification.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

namespace Implementation

/-- Compatibility of the forward identity comparison with changed-cospan cone
comparisons. -/
private theorem changeCospan.mapId.hom_comm
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    ((S.changeCospan ψ).toPseudoCone.comparison S.pt).map
          (𝟙 (𝟙 S.pt)) ≫
        PseudoPullbackCone.fac (𝟙 (S.changeCospan ψ)) =
      PseudoPullbackCone.fac (changeCospan.map ψ (𝟙 S)) := sorry
/- Proof strategy: expand `changeCospan.fac`; cancel the presentation isomorphisms and use the
generic `ColaxCostructuredArrow.postcompose.mapId` comparison. -/

/-- The forward identity comparison for readable change of cospan. -/
private def changeCospan.mapId.hom
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    changeCospan.map ψ (𝟙 S) ⟶ 𝟙 (S.changeCospan ψ) :=
  PseudoPullbackCone.hom₂Mk (𝟙 (𝟙 S.pt))
    (changeCospan.mapId.hom_comm ψ S)

/-- Compatibility of the inverse identity comparison with changed-cospan cone
comparisons. -/
private theorem changeCospan.mapId.inv_comm
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    ((S.changeCospan ψ).toPseudoCone.comparison S.pt).map
          (𝟙 (𝟙 S.pt)) ≫
        PseudoPullbackCone.fac (changeCospan.map ψ (𝟙 S)) =
      PseudoPullbackCone.fac (𝟙 (S.changeCospan ψ)) := sorry
/- Proof strategy: use the inverse generic `ColaxCostructuredArrow.postcompose.mapId` comparison through the
same presentation conjugations. -/

/-- The inverse identity comparison for readable change of cospan. -/
private def changeCospan.mapId.inv
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    𝟙 (S.changeCospan ψ) ⟶ changeCospan.map ψ (𝟙 S) :=
  PseudoPullbackCone.hom₂Mk (𝟙 (𝟙 S.pt))
    (changeCospan.mapId.inv_comm ψ S)

/-- The forward and inverse identity comparisons for readable change of cospan cancel on the
mapped identity. -/
private theorem changeCospan.mapId.hom_inv_id
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    changeCospan.mapId.hom ψ S ≫ changeCospan.mapId.inv ψ S =
      𝟙 (changeCospan.map ψ (𝟙 S)) := sorry
/- Proof strategy: apply `PseudoPullbackCone.hom₂_ext`; every apex component is an
identity. -/

/-- The inverse and forward identity comparisons for readable change of cospan cancel on the
target identity. -/
private theorem changeCospan.mapId.inv_hom_id
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    changeCospan.mapId.inv ψ S ≫ changeCospan.mapId.hom ψ S =
      𝟙 (𝟙 (S.changeCospan ψ)) := sorry
/- Proof strategy: apply `PseudoPullbackCone.hom₂_ext`; every apex component is an
identity. -/

end Implementation

/-- The identity comparison for readable change of cospan. Its apex component is an explicit
identity `2`-morphism. -/
def changeCospan.mapId
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    changeCospan.map ψ (𝟙 S) ≅ 𝟙 (S.changeCospan ψ) where
  hom := Implementation.changeCospan.mapId.hom ψ S
  inv := Implementation.changeCospan.mapId.inv ψ S
  hom_inv_id := Implementation.changeCospan.mapId.hom_inv_id ψ S
  inv_hom_id := Implementation.changeCospan.mapId.inv_hom_id ψ S

/-- The apex cell of the forward identity comparison for readable change of cospan is the
identity. -/
@[simp]
theorem changeCospan.mapId.hom.apex
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    PseudoPullbackCone.map₂ (changeCospan.mapId ψ S).hom =
      𝟙 (𝟙 S.pt) := sorry
/- Proof strategy: unfold `changeCospan.mapId` and its forward helper, then apply
`PseudoPullbackCone.hom₂Mk_map₂`. -/

/-- The apex cell of the inverse identity comparison for readable change of cospan is the
identity. -/
@[simp]
theorem changeCospan.mapId.inv.apex
    (ψ : CospanTransform f g f' g')
    (S : PseudoPullbackCone f g) :
    PseudoPullbackCone.map₂ (changeCospan.mapId ψ S).inv =
      𝟙 (𝟙 S.pt) := sorry
/- Proof strategy: unfold `changeCospan.mapId` and its inverse helper, then apply
`PseudoPullbackCone.hom₂Mk_map₂`. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
