/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.GysinAtInfinity
public import ReasLib.AlgebraicGeometry.BivariantClass.ProperPushforward

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.GysinAtInfinity

/-- A composite compactification is an isomorphism over the affine part when both
factors are isomorphisms over the corresponding affine opens. -/
instance compIsIsoOverAffine
    {S W W' : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) (g : W' ⟶ W)
    [IsIso (b ∣_ affinePart X)] [IsIso (g ∣_ (b ⁻¹ᵁ affinePart X))] :
    IsIso ((g ≫ b) ∣_ affinePart X) := sorry

/-- A cartesian map between infinity fibres commutes with their canonical maps to `X`. -/
theorem infinityMap_toX_of_isPullback
    {S W W' : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) (g : W' ⟶ W)
    (gInf : infinityFiber X (g ≫ b) ⟶ infinityFiber X b)
    (square : IsPullback (infinityInclusion X (g ≫ b)).left gInf.left
      g (infinityInclusion X b).left) :
    gInf ≫ infinityToX X b = infinityToX X (g ≫ b) := sorry

end AlgebraicGeometry.BivariantClass.GysinAtInfinity

namespace AlgebraicGeometry.BivariantClass

/-- Proper pushforward along a modification that is an isomorphism over the affine
part carries its canonical Gysin-at-infinity class to the canonical class of the
original compactification. -/
@[stacks 0FAQ]
theorem gysinAtInfinity_pushforward_of_modification
    {S W W' : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ GysinAtInfinity.affinePart X)]
    (g : W' ⟶ W) [IsProper g]
    [IsIso (g ∣_ (b ⁻¹ᵁ GysinAtInfinity.affinePart X))]
    (gInf : GysinAtInfinity.infinityFiber X (g ≫ b) ⟶
      GysinAtInfinity.infinityFiber X b)
    (square : IsPullback (GysinAtInfinity.infinityInclusion X (g ≫ b)).left gInf.left
      g (GysinAtInfinity.infinityInclusion X b).left)
    [IsProper gInf.left] :
    properPushforward δ gInf (GysinAtInfinity.infinityToX X b) 0
        ((GysinAtInfinity.infinityMap_toX_of_isPullback X b g gInf square).symm ▸
          gysinAtInfinity δ X (g ≫ b)) =
      gysinAtInfinity δ X b := sorry

end AlgebraicGeometry.BivariantClass
