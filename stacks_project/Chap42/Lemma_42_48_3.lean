module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.GysinAtInfinity.Modification
public import stacks_project.Chap42.Lemma_42_48_1
public import stacks_project.Chap42.Lemma_42_29_8

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/- Lemma 42.48.3: proper pushforward along a modification that is an isomorphism over
the affine part carries its canonical Gysin-at-infinity class to the canonical class of
the original compactification. -/
@[stacks 0FAQ] #check
  (AlgebraicGeometry.BivariantClass.gysinAtInfinity_pushforward_of_modification :
    ∀ {S W W' : Scheme.{u}} [UniversallyCatenary S]
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
    [IsProper gInf.left],
    properPushforward δ gInf (GysinAtInfinity.infinityToX X b) 0
        ((GysinAtInfinity.infinityMap_toX_of_isPullback X b g gInf square).symm ▸
          gysinAtInfinity δ X (g ≫ b)) =
      gysinAtInfinity δ X b)

end AlgebraicGeometry.BivariantClass
