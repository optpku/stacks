/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.DualObstruction.NaiveCotangent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect

/-!
# Versality for dual obstruction data

Pointwise versality for an affine object with dual obstruction data, and its
spread from a closed finite-type point to an open neighbourhood.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]

namespace DualObstruction

/-- The affine object of dual obstruction data is versal at a point when its
canonical residue-field morphism of predeformation categories is smooth. -/
abbrev IsVersalAt (𝒟 : DualObstruction X)
    (u0 : Spec (CommRingCat.of 𝒟.carrier)) : Prop :=
  @AlgebraicGeometry.GroupoidsOver.IsVersalAt S _ X _ 𝒟.toS
    𝒟.locallyOfFiniteType 𝒟.obj 𝒟.over_obj u0

/-- For connecting-compatible dual obstruction data with a perfect complex,
versality at a closed finite-type point extends to every finite-type point
of an open neighbourhood. -/
@[stacks 07YZ]
theorem exists_isVersalAt_nhd_of_closed (𝒟 : DualObstruction X)
    (h_connecting : IsConnectingCompatible 𝒟)
    (h_perfect : DerivedCategory.IsPerfect 𝒟.derivedObject)
    (u0 : Spec (CommRingCat.of 𝒟.carrier)) [IsFiniteTypePoint u0]
    [𝒟.IsVersalAt u0] (h_closed : IsClosed {u0}) :
    ∃ U' : Opens (Spec (CommRingCat.of 𝒟.carrier)),
      u0 ∈ U' ∧
        ∀ u, u ∈ U' → IsFiniteTypePoint u →
          𝒟.IsVersalAt u :=
  sorry

end DualObstruction

end AlgebraicGeometry.GroupoidsOver
