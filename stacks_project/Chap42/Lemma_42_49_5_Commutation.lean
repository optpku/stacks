/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_47_6_Commutation
public import stacks_project.Chap42.Lemma_42_48_5
public import stacks_project.Chap42.Lemma_42_49_3_AtZero

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- The inverse image of a closed immersion in `X` is a closed immersion into the
infinity fibre. -/
instance infinityCenterToInfinityFiberIsClosedImmersion
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) :
    IsClosedImmersion
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left := sorry

/-- Commutation of a localized class with every homogeneous class into the infinity
fibre is preserved by the `classAtZero` construction. -/
theorem classAtZero_commute
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (p : ℤ)
    (localized : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) p)
    (localized_commute :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (f : Y ⟶ BivariantClass.GysinAtInfinity.infinityFiber X b)
        [LocallyOfFiniteType f.left]
        (q : ℤ) (c : BivariantClass delta f q),
        BivariantClass.Commute delta f
          (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) c localized)
    {Y : Over S} [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) [LocallyOfFiniteType f.left]
    (q : ℤ) (c : BivariantClass delta f q) :
    BivariantClass.Commute delta f
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) c
      (classAtZero delta i b p localized) := sorry

end AlgebraicGeometry.LocalizedChern
