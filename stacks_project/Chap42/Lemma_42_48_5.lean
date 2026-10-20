module

import ReasLib.AlgebraicGeometry.BivariantClass.GysinAtInfinity.Commutation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/- Lemma 42.48.5: in the setup of Lemma 42.48.1, the Gysin-at-infinity
class commutes with every bivariant class for a locally finite-type morphism. -/
@[stacks 0FAS] #check
  (AlgebraicGeometry.BivariantClass.gysinAtInfinity_commute :
    ∀ {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
      [IsIso (b ∣_ GysinAtInfinity.affinePart X)]
      {Y : Over S} [LocallyOfFiniteType Y.hom]
      (f : Y ⟶ Over.mk X.hom) [LocallyOfFiniteType f.left]
      (q : ℤ) (c : BivariantClass δ f q),
      Commute δ f (GysinAtInfinity.infinityToX X b) c (gysinAtInfinity δ X b))

end AlgebraicGeometry.BivariantClass
