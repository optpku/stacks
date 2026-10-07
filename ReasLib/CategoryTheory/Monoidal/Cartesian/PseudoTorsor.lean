module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G : C} [GrpObj G]

/-- A module object is a pseudo-torsor when its shear morphism
`(g, x) ↦ (g • x, x)` is an isomorphism. -/
class IsPseudoTorsor (X : Mod C G) : Prop where
  /-- The shear morphism of a pseudo-torsor is an isomorphism. -/
  isIso_leftSMul : IsIso (ModObj.leftSMul G X.X)

namespace IsPseudoTorsor

/-- The shear morphism of a pseudo-torsor is an isomorphism. -/
instance instIsIsoLeftSMul (X : Mod C G) [IsPseudoTorsor X] :
    IsIso (ModObj.leftSMul G X.X) := sorry

/-- Pseudo-torsorhood transports across an equivariant isomorphism. -/
theorem ofIso {X Y : Mod C G} [IsPseudoTorsor X] (e : X ≅ Y) :
    IsPseudoTorsor Y := sorry

end IsPseudoTorsor

/-- The regular left action of a group object is a pseudo-torsor. -/
instance instIsPseudoTorsorRegular : IsPseudoTorsor (regular G) := sorry

/-- Pseudo-torsorhood is equivalent to invertibility of the shear morphism. -/
theorem isPseudoTorsor_iff (X : Mod C G) :
    IsPseudoTorsor X ↔ IsIso (ModObj.leftSMul G X.X) := sorry

/-- Pseudo-torsorhood is equivalent to unique transitivity on generalized points. -/
theorem isPseudoTorsor_iff_forall_existsUnique_smul (X : Mod C G) :
    IsPseudoTorsor X ↔
      ∀ (Z : C) (x y : Z ⟶ X.X), ∃! g : Z ⟶ G, g • x = y := sorry

/-- A module object is trivial when it is equivariantly isomorphic to the regular left action. -/
abbrev IsTrivial (X : Mod C G) : Prop :=
  Nonempty (regular G ≅ X)

/-- Triviality is existence of an equivariant isomorphism from the regular left action. -/
theorem isTrivial_iff (X : Mod C G) :
    IsTrivial X ↔ Nonempty (regular G ≅ X) := sorry

namespace IsTrivial

/-- Every trivial module object is a pseudo-torsor. -/
theorem isPseudoTorsor {X : Mod C G} (hX : IsTrivial X) :
    IsPseudoTorsor X := sorry

end IsTrivial

end CategoryTheory.Mod
