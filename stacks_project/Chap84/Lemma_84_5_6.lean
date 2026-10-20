module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallToBig.Proper
import StacksCheckRecall

/-!
# Proper direct images on small and big étale sites

For a proper morphism of algebraic spaces, small and big étale direct images
agree after inverse image along `π`, on sheaves of sets, on `D⁺` with torsion
cohomology, and on all of `D` when the morphism is finite.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open CategoryTheory CategoryTheory.Sheaf

universe u

/- Lemma 84.5.6 (1): the canonical comparison on sheaves of sets is invertible
for a proper morphism of algebraic spaces over any scheme. -/
@[stacks 0DGD] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.proper_smallBigPushforward_isIso :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (f : Y ⟶ X) → [Proper f] →
      IsIso (SmallToBig.smallBigPushforwardHom f))

/- Part (2): the canonical comparison is invertible on bounded-below complexes
whose cohomology sheaves are locally torsion. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.proper_smallBigDerivedPushforward_plus_isIso :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (f : Y ⟶ X) → [Proper f] →
      (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})) →
      DerivedCategory.Plus.cohomologyIn
        (IsLocallyTorsion :
          ObjectProperty (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})) K →
      IsIso ((SmallToBig.plusSmallBigPushforwardHom f).app K))

/- Part (3): for a finite morphism, the canonical comparison is invertible on
every unbounded complex, with no torsion restriction. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.finite_smallBigDerivedPushforward_isIso :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (f : Y ⟶ X) →
      [IsGrothendieckAbelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})] →
      [IsGrothendieckAbelian (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1})] →
      [IsFinite f] →
      (K : DerivedCategory (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})) →
      IsIso ((SmallToBig.unboundedSmallBigPushforwardHom f).app K))
