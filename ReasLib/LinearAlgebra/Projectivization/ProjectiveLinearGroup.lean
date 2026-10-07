module

public import Mathlib.LinearAlgebra.Projectivization.Action

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

universe u v

/-- The projective general linear group is the effective image of the general linear group
acting on projective space. -/
abbrev ProjectiveGeneralLinearGroup
    (K : Type u) (V : Type v) [DivisionRing K] [AddCommGroup V] [Module K V] : Type _ :=
  ((MulAction.toPermHom (LinearMap.GeneralLinearGroup K V) (ℙ K V)).range :
    Subgroup (Equiv.Perm (ℙ K V)))

namespace ProjectiveGeneralLinearGroup

variable (K : Type u) (V : Type v) [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The canonical homomorphism from the general linear group to the effective projective
general linear group. -/
def mk : LinearMap.GeneralLinearGroup K V →* ProjectiveGeneralLinearGroup K V :=
  (MulAction.toPermHom (LinearMap.GeneralLinearGroup K V) (ℙ K V)).rangeRestrict

/-- The projective action of the canonical image of a linear automorphism agrees with its
usual action on projective space. -/
theorem mk_smul (g : LinearMap.GeneralLinearGroup K V) (x : ℙ K V) :
    mk K V g • x = g • x := sorry

/-- Every element of the effective projective general linear group is represented by a
linear automorphism. -/
theorem mk_surjective : Function.Surjective (mk K V) := sorry

end ProjectiveGeneralLinearGroup

/-- The effective projective general linear group acts doubly transitively on projective
space. -/
instance projectiveGeneralLinearGroup_is_two_pretransitive
    (K : Type u) (V : Type v) [DivisionRing K] [AddCommGroup V] [Module K V] :
    MulAction.IsMultiplyPretransitive (ProjectiveGeneralLinearGroup K V) (ℙ K V) 2 := sorry

end Projectivization
