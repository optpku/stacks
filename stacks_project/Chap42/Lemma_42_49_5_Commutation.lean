/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap42.Lemma_42_35_4_Additive
public import stacks_project.Chap42.Lemma_42_47_6_Commutation
public import stacks_project.Chap42.Lemma_42_48_5
public import stacks_project.Chap42.Lemma_42_49_3_AtZero
public import ReasLib.AlgebraicGeometry.LocalizedChern.Compactification.Commutation

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- The inverse image of a closed center in the infinity fiber is a closed
subscheme of that fiber. -/
theorem infinityCenterToInfinityFiberIsClosedImmersion
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) :
    IsClosedImmersion
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left := by
  exact Scheme.overPullbackFstHomMkIsClosedImmersion
    (BivariantClass.GysinAtInfinity.infinityToX X b) i

/- Compatibility checks for declarations moved to the reusable owner. -/
#check (AlgebraicGeometry.Scheme.overPullbackFstIsClosedImmersion :
  ∀ {S : Scheme.{u}} {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsClosedImmersion g.left], IsClosedImmersion (pullback.fst f g).left)

#check (AlgebraicGeometry.Scheme.overPullbackFstHomMkIsClosedImmersion :
  ∀ {S : Scheme.{u}} {A X : Over S} {Z : Scheme.{u}}
    (f : A ⟶ Over.mk X.hom) (i : Z ⟶ X.left) [IsClosedImmersion i],
    IsClosedImmersion
      (pullback.fst f (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left)

#check (AlgebraicGeometry.LocalizedChern.isCompactificationLocalization_commute :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t] (p : ℤ)
    (ambient : BivariantClass delta
      (𝟙 (BivariantClass.GysinAtInfinity.compactification X b)) p)
    (output : BivariantClass delta
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p)
    (houtput : IsCompactificationLocalization delta i b t p ambient output)
    (ambient_commute : ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
      (g : Y ⟶ BivariantClass.GysinAtInfinity.compactification X b)
      [LocallyOfFiniteType g.left] (q : ℤ)
      (c : BivariantClass delta g q),
      BivariantClass.Commute delta g
        (𝟙 (BivariantClass.GysinAtInfinity.compactification X b)) c ambient),
    ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
      (f : Y ⟶ X) [LocallyOfFiniteType f.left] (q : ℤ)
      (c : BivariantClass delta f q),
      BivariantClass.Commute delta f
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) c output)

end AlgebraicGeometry.LocalizedChern
