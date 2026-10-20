module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion
import StacksCheckRecall

/-! # Comparison of small and spaces étale sites

@stack 03G1

Both source conclusions use the public canonical site inclusion and exact small-site topology.
-/

@[expose] public section

universe u

/- Lemma 66.18.3. The canonical inclusion of schemes étale over an algebraic space
into algebraic spaces étale over it is special cocontinuous. -/
@[stacks 03G1]
#check (AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces_isSpecialCocontinuous :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    (AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces X).IsSpecialCocontinuous
      (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X)
      (AlgebraicGeometry.AlgebraicSpace.spacesEtaleTopology X))

/- Lemma 66.18.3. The induced cocontinuous direct image is an equivalence of
categories of set-valued sheaves. -/
@[stacks 03G1]
#check (AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces_directImage_isEquivalence :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    ((AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces X).sheafPushforwardCocontinuous
      (Type (u + 1)) (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X)
      (AlgebraicGeometry.AlgebraicSpace.spacesEtaleTopology X)).IsEquivalence)
