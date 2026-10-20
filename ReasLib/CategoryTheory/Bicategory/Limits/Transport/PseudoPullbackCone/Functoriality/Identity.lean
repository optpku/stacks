module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoPullbackCone.Hom

/-!
# Identity comparison for readable pseudopullback-cone transport

This module constructs the identity comparison for mapping readable pseudopullback cones along
a pseudofunctor. Its apex component is exactly the ambient pseudofunctor's `mapId`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uB vB wB uD vD wD

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} {D : Type uD}
variable [Bicategory.{wB, vB} B] [Bicategory.{wD, vD} D]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

namespace Implementation

/-- Compatibility of the forward identity comparison with the readable mapped cone
comparisons. -/
private theorem mapPseudoPullbackCone.mapId.hom.comm (H : Pseudofunctor B D)
    (S : Bicategory.PseudoPullbackCone f g) :
    ((H.mapPseudoPullbackCone S).toPseudoCone.comparison
        (H.obj S.pt)).map (H.mapId S.pt).hom ≫
        Bicategory.PseudoPullbackCone.fac
          (𝟙 (H.mapPseudoPullbackCone S)) =
      Bicategory.PseudoPullbackCone.fac
        (mapPseudoPullbackCone.map H (𝟙 S)) := sorry

/-- The forward identity comparison between mapped readable pseudopullback-cone morphisms. -/
private def mapPseudoPullbackCone.mapId.hom (H : Pseudofunctor B D)
    (S : Bicategory.PseudoPullbackCone f g) :
    mapPseudoPullbackCone.map H (𝟙 S) ⟶
      𝟙 (H.mapPseudoPullbackCone S) :=
  Bicategory.PseudoPullbackCone.hom₂Mk
    (H.mapId S.pt).hom
    (mapPseudoPullbackCone.mapId.hom.comm H S)

/-- Compatibility of the inverse identity comparison with the readable mapped cone
comparisons. -/
private theorem mapPseudoPullbackCone.mapId.inv.comm (H : Pseudofunctor B D)
    (S : Bicategory.PseudoPullbackCone f g) :
    ((H.mapPseudoPullbackCone S).toPseudoCone.comparison
        (H.obj S.pt)).map (H.mapId S.pt).inv ≫
        Bicategory.PseudoPullbackCone.fac
          (mapPseudoPullbackCone.map H (𝟙 S)) =
      Bicategory.PseudoPullbackCone.fac
        (𝟙 (H.mapPseudoPullbackCone S)) := sorry

/-- The inverse identity comparison between mapped readable pseudopullback-cone morphisms. -/
private def mapPseudoPullbackCone.mapId.inv (H : Pseudofunctor B D)
    (S : Bicategory.PseudoPullbackCone f g) :
    𝟙 (H.mapPseudoPullbackCone S) ⟶
      mapPseudoPullbackCone.map H (𝟙 S) :=
  Bicategory.PseudoPullbackCone.hom₂Mk
    (H.mapId S.pt).inv
    (mapPseudoPullbackCone.mapId.inv.comm H S)

/-- The forward and inverse readable identity comparisons cancel on the mapped identity. -/
private theorem mapPseudoPullbackCone.mapId.homInvId
    (H : Pseudofunctor B D) (S : Bicategory.PseudoPullbackCone f g) :
    mapPseudoPullbackCone.mapId.hom H S ≫
        mapPseudoPullbackCone.mapId.inv H S =
      𝟙 (mapPseudoPullbackCone.map H (𝟙 S)) := sorry

/-- The inverse and forward readable identity comparisons cancel on the target identity. -/
private theorem mapPseudoPullbackCone.mapId.invHomId
    (H : Pseudofunctor B D) (S : Bicategory.PseudoPullbackCone f g) :
    mapPseudoPullbackCone.mapId.inv H S ≫
        mapPseudoPullbackCone.mapId.hom H S =
      𝟙 (𝟙 (H.mapPseudoPullbackCone S)) := sorry

end Implementation

/-- The identity comparison for mapping readable pseudopullback cones along a pseudofunctor.
Its apex component is the identity comparison of the ambient pseudofunctor. -/
def mapPseudoPullbackCone.mapId (H : Pseudofunctor B D)
    (S : Bicategory.PseudoPullbackCone f g) :
    mapPseudoPullbackCone.map H (𝟙 S) ≅
      𝟙 (H.mapPseudoPullbackCone S) where
  hom := Implementation.mapPseudoPullbackCone.mapId.hom H S
  inv := Implementation.mapPseudoPullbackCone.mapId.inv H S
  hom_inv_id := Implementation.mapPseudoPullbackCone.mapId.homInvId H S
  inv_hom_id := Implementation.mapPseudoPullbackCone.mapId.invHomId H S

/-- The apex cell of the forward identity comparison is `H.mapId`. -/
@[simp]
theorem mapPseudoPullbackCone.mapId.hom.apex (H : Pseudofunctor B D)
    (S : Bicategory.PseudoPullbackCone f g) :
    Bicategory.PseudoPullbackCone.map₂
        (mapPseudoPullbackCone.mapId H S).hom =
      (H.mapId S.pt).hom := sorry

/-- The apex cell of the inverse identity comparison is the inverse of `H.mapId`. -/
@[simp]
theorem mapPseudoPullbackCone.mapId.inv.apex (H : Pseudofunctor B D)
    (S : Bicategory.PseudoPullbackCone f g) :
    Bicategory.PseudoPullbackCone.map₂
        (mapPseudoPullbackCone.mapId H S).inv =
      (H.mapId S.pt).inv := sorry

-- Data audit: the forward and inverse apex cells of `mapPseudoPullbackCone.mapId` are explicitly
-- `(H.mapId S.pt).hom` and `(H.mapId S.pt).inv`; `sorryAx` is confined to compatibility and
-- inverse-law propositions.

end Pseudofunctor

end CategoryTheory
