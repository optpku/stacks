/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone

/-!
# Mapping readable pseudopullback cones

This module contains the object-level action of a pseudofunctor on the readable four-field
presentation of a pseudopullback cone. It is independent of the walking-cospan normalization,
cone morphisms, and universal properties.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe uB vB wB uD vD wD

namespace CategoryTheory

open Bicategory

namespace Pseudofunctor

variable {B : Type uB} {D : Type uD}
variable [Bicategory.{wB, vB} B] [Bicategory.{wD, vD} D]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- Map a readable pseudopullback cone along a pseudofunctor. The comparison is conjugated by
the pseudofunctor's composition constraints, so no strictness assumption is required. -/
def mapPseudoPullbackCone (H : Pseudofunctor B D)
    (P : Bicategory.PseudoPullbackCone f g) :
    Bicategory.PseudoPullbackCone (H.map f) (H.map g) where
  pt := H.obj P.pt
  fst := H.map P.fst
  snd := H.map P.snd
  iso := (H.mapComp P.fst f).symm ≪≫ H.map₂Iso P.iso ≪≫ H.mapComp P.snd g

/-- The apex of a readable pseudopullback cone mapped along a pseudofunctor. -/
@[simp]
theorem mapPseudoPullbackCone.pt (H : Pseudofunctor B D)
    (P : Bicategory.PseudoPullbackCone f g) :
    (H.mapPseudoPullbackCone P).pt = H.obj P.pt := sorry

/-- The left leg of a readable pseudopullback cone mapped along a pseudofunctor. -/
@[simp]
theorem mapPseudoPullbackCone.fst (H : Pseudofunctor B D)
    (P : Bicategory.PseudoPullbackCone f g) :
    (H.mapPseudoPullbackCone P).fst = H.map P.fst := sorry

/-- The right leg of a readable pseudopullback cone mapped along a pseudofunctor. -/
@[simp]
theorem mapPseudoPullbackCone.snd (H : Pseudofunctor B D)
    (P : Bicategory.PseudoPullbackCone f g) :
    (H.mapPseudoPullbackCone P).snd = H.map P.snd := sorry

/-- The square comparison of a readable pseudopullback cone mapped along a pseudofunctor. -/
@[simp]
theorem mapPseudoPullbackCone.iso (H : Pseudofunctor B D)
    (P : Bicategory.PseudoPullbackCone f g) :
    (H.mapPseudoPullbackCone P).iso =
      (H.mapComp P.fst f).symm ≪≫ H.map₂Iso P.iso ≪≫
        H.mapComp P.snd g := sorry

/-- The forward square cell of a mapped readable pseudopullback cone. -/
@[simp]
theorem mapPseudoPullbackCone.iso.hom (H : Pseudofunctor B D)
    (P : Bicategory.PseudoPullbackCone f g) :
    (H.mapPseudoPullbackCone P).iso.hom =
      (H.mapComp P.fst f).inv ≫
        H.map₂ P.iso.hom ≫ (H.mapComp P.snd g).hom := sorry

/-- The inverse square cell of a mapped readable pseudopullback cone. -/
@[simp]
theorem mapPseudoPullbackCone.iso.inv (H : Pseudofunctor B D)
    (P : Bicategory.PseudoPullbackCone f g) :
    (H.mapPseudoPullbackCone P).iso.inv =
      (H.mapComp P.snd g).inv ≫
        H.map₂ P.iso.inv ≫ (H.mapComp P.fst f).hom := sorry

-- Data audit: `mapPseudoPullbackCone` depends only on `propext`, `Classical.choice`, and
-- `Quot.sound`; in particular, its apex, legs, and square comparison do not depend on
-- `sorryAx`.

end Pseudofunctor

end CategoryTheory
