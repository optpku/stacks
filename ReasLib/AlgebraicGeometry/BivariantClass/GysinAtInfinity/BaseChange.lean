/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.GysinAtInfinity
public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveLineFamily.BaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- The Gysin-at-infinity class obtained from a locally finite-type base change of a
compactification is the bivariant restriction of the original class. -/
theorem gysinAtInfinity_baseChange
    {S W W' : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X X' : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (g : Over.mk X'.hom ⟶ Over.mk X.hom) [LocallyOfFiniteType g.left]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ GysinAtInfinity.affinePart X)]
    (b' : W' ⟶ ProjectiveLineFamily.space X') [IsProper b']
    [IsIso (b' ∣_ GysinAtInfinity.affinePart X')]
    (h : GysinAtInfinity.compactification X' b' ⟶
      GysinAtInfinity.compactification X b)
    (hb : IsPullback h.left b' b (ProjectiveLineFamily.map g))
    (j : GysinAtInfinity.infinityFiber X' b' ⟶
      GysinAtInfinity.infinityFiber X b)
    (hj : j ≫ GysinAtInfinity.infinityInclusion X b =
      GysinAtInfinity.infinityInclusion X' b' ≫ h)
    (infinitySquare : IsPullback j.left (GysinAtInfinity.infinityToX X' b').left
      (GysinAtInfinity.infinityToX X b).left g.left) :
    gysinAtInfinity δ X' b' =
      restrict δ j (GysinAtInfinity.infinityToX X' b') g infinitySquare 0
        (gysinAtInfinity δ X b) := sorry

end AlgebraicGeometry.BivariantClass
