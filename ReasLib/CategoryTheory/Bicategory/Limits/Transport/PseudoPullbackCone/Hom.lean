module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Hom.Computations
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoPullbackCone.Comparison

/-!
# Mapping morphisms of readable pseudopullback cones

This module maps morphisms and `2`-morphisms of readable pseudopullback cones. Their comparison
modifications are obtained from generic pseudocone transport by conjugating at the three
walking-cospan vertices with the presentation comparisons.
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

/-- The components used to assemble the mapped comparison of a readable
pseudopullback-cone morphism. -/
private def mapPseudoPullbackCone.fac.app (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    ∀ j : LocallyDiscrete Limits.WalkingCospan,
      H.map (Bicategory.PseudoPullbackCone.map u) ≫
          (H.mapPseudoPullbackCone T).toPseudoCone.π.app j ⟶
        (H.mapPseudoPullbackCone S).toPseudoCone.π.app j
  | ⟨Limits.WalkingCospan.one⟩ =>
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.centerIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.one) ≫
        (mapPseudoPullbackCone.presentation.centerIso H S).inv
  | ⟨Limits.WalkingCospan.left⟩ =>
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.leftIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.left) ≫
        (mapPseudoPullbackCone.presentation.leftIso H S).inv
  | ⟨Limits.WalkingCospan.right⟩ =>
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.rightIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.right) ≫
        (mapPseudoPullbackCone.presentation.rightIso H S).inv

/-- The conjugated generic comparison components satisfy modification naturality. -/
private theorem mapPseudoPullbackCone.fac.app.naturality
    (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    ∀ {a b : LocallyDiscrete Limits.WalkingCospan} (h : a ⟶ b),
      (Pseudofunctor.const
          (LocallyDiscrete Limits.WalkingCospan) (H.obj S.pt)).map h ◁
            mapPseudoPullbackCone.fac.app H u b ≫
          ((H.mapPseudoPullbackCone S).toPseudoCone.π.naturality h).hom =
        ((((H.mapPseudoPullbackCone T).toPseudoCone.comparison
            (H.obj S.pt)).obj
              (H.map (Bicategory.PseudoPullbackCone.map u))).naturality h).hom ≫
          mapPseudoPullbackCone.fac.app H u a ▷
            (Bicategory.cospan (H.map f) (H.map g)).map h := sorry

end Implementation

/-- The comparison modification carried by a mapped readable pseudopullback-cone morphism.

Its three components are the generic mapped comparison conjugated by the corresponding
presentation isomorphisms, so this readable facade introduces no second transport convention. -/
def mapPseudoPullbackCone.fac (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    ((H.mapPseudoPullbackCone T).toPseudoCone.comparison
        (H.obj S.pt)).obj
          (H.map (Bicategory.PseudoPullbackCone.map u)) ⟶
      (H.mapPseudoPullbackCone S).toPseudoCone.π :=
  ⟨{
    app := Implementation.mapPseudoPullbackCone.fac.app H u
    naturality := Implementation.mapPseudoPullbackCone.fac.app.naturality H u }⟩

/-- The left component of the readable mapped comparison is the generic comparison conjugated
by the left-vertex presentation isomorphisms. -/
@[simp]
theorem mapPseudoPullbackCone.fac.app.left (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    (mapPseudoPullbackCone.fac H u).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.leftIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.left) ≫
        (mapPseudoPullbackCone.presentation.leftIso H S).inv := sorry

/-- The right component of the readable mapped comparison is the generic comparison conjugated
by the right-vertex presentation isomorphisms. -/
@[simp]
theorem mapPseudoPullbackCone.fac.app.right (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    (mapPseudoPullbackCone.fac H u).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.rightIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.right) ≫
        (mapPseudoPullbackCone.presentation.rightIso H S).inv := sorry

/-- The central component of the readable mapped comparison is the generic comparison
conjugated by the central presentation isomorphisms. -/
@[simp]
theorem mapPseudoPullbackCone.fac.app.center (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    (mapPseudoPullbackCone.fac H u).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.one) =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.centerIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.one) ≫
        (mapPseudoPullbackCone.presentation.centerIso H S).inv := sorry

/-- Map a morphism of readable pseudopullback cones along a pseudofunctor. Its apex map is the
image of the original apex map, and its comparison is `mapPseudoPullbackCone.fac`. -/
def mapPseudoPullbackCone.map (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    H.mapPseudoPullbackCone S ⟶ H.mapPseudoPullbackCone T :=
  Bicategory.PseudoPullbackCone.homMk
    (H.map (Bicategory.PseudoPullbackCone.map u))
    (mapPseudoPullbackCone.fac H u)

/-- The apex map of a mapped readable pseudopullback-cone morphism. -/
@[simp]
theorem mapPseudoPullbackCone.map.apex (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    Bicategory.PseudoPullbackCone.map (mapPseudoPullbackCone.map H u) =
      H.map (Bicategory.PseudoPullbackCone.map u) := sorry

/-- The comparison modification of a mapped readable pseudopullback-cone morphism. -/
@[simp]
theorem mapPseudoPullbackCone.map.fac (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    Bicategory.PseudoPullbackCone.fac (mapPseudoPullbackCone.map H u) =
      mapPseudoPullbackCone.fac H u := sorry

/-- The left-leg comparison cell of a mapped readable pseudopullback-cone morphism. -/
@[simp]
theorem mapPseudoPullbackCone.map.fstFac (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    Bicategory.PseudoPullbackCone.fstFac (mapPseudoPullbackCone.map H u) =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.leftIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.left) ≫
        (mapPseudoPullbackCone.presentation.leftIso H S).inv := sorry

/-- The right-leg comparison cell of a mapped readable pseudopullback-cone morphism. -/
@[simp]
theorem mapPseudoPullbackCone.map.sndFac (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    Bicategory.PseudoPullbackCone.sndFac (mapPseudoPullbackCone.map H u) =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.rightIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.right) ≫
        (mapPseudoPullbackCone.presentation.rightIso H S).inv := sorry

namespace Implementation

/-- Compatibility of the mapped readable apex cell with the conjugated comparison
modifications. -/
private theorem mapPseudoPullbackCone.map₂.comm (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v) :
    ((H.mapPseudoPullbackCone T).toPseudoCone.comparison
        (H.obj S.pt)).map
          (H.map₂ (Bicategory.PseudoPullbackCone.map₂ η)) ≫
        Bicategory.PseudoPullbackCone.fac
          (mapPseudoPullbackCone.map H v) =
      Bicategory.PseudoPullbackCone.fac
        (mapPseudoPullbackCone.map H u) := sorry

end Implementation

/-- Map a `2`-morphism of readable pseudopullback cones along a pseudofunctor. Its apex cell is
the image of the original apex cell. -/
def mapPseudoPullbackCone.map₂ (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v) :
    mapPseudoPullbackCone.map H u ⟶ mapPseudoPullbackCone.map H v :=
  Bicategory.PseudoPullbackCone.hom₂Mk
    (H.map₂ (Bicategory.PseudoPullbackCone.map₂ η))
    (Implementation.mapPseudoPullbackCone.map₂.comm H η)

/-- The apex cell of a mapped readable pseudopullback-cone `2`-morphism. -/
@[simp]
theorem mapPseudoPullbackCone.map₂.apex (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v) :
    Bicategory.PseudoPullbackCone.map₂
        (mapPseudoPullbackCone.map₂ H η) =
      H.map₂ (Bicategory.PseudoPullbackCone.map₂ η) := sorry

-- Data audit: every component of `mapPseudoPullbackCone.fac` is an explicit conjugate of
-- `mapPseudoCone.fac`; the apex data of `mapPseudoPullbackCone.map` and
-- `mapPseudoPullbackCone.map₂` are respectively `H.map` and `H.map₂` of the original apex
-- data. Their `sorryAx` dependencies are confined to naturality and compatibility propositions.

end Pseudofunctor

end CategoryTheory
