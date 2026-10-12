/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_49_1
public import stacks_project.Chap42.Lemma_42_49_5_Commutation

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- Lemma 42.49.5 (1): the Newton bivariant class at zero commutes with every
homogeneous bivariant class on a locally finite-type morphism into `X`. -/
@[stacks 0FAW]
theorem newtonClassAtZero_commute
    {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ} [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (p : ℕ)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
    (newtonClass :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (g : Y ⟶ BivariantClass.GysinAtInfinity.compactification X b)
        [LocallyOfFiniteType g.left] (r : ℕ),
        BivariantClass delta (𝟙 Y) (r : ℤ))
    (newtonClass_naturality :
      ∀ {Y Y' : Over S} [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Y'.hom]
        (g : Y ⟶ BivariantClass.GysinAtInfinity.compactification X b)
        [LocallyOfFiniteType g.left] (h : Y' ⟶ Y) [LocallyOfFiniteType h.left] (r : ℕ),
        BivariantClass.restrict delta h (𝟙 Y') h IsPullback.of_id_snd
            (r : ℤ) (newtonClass g r) =
          newtonClass (h ≫ g) r)
    (newtonClass_vanishes :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (g : Y ⟶ BivariantClass.GysinAtInfinity.compactification X b)
        [LocallyOfFiniteType g.left],
        IsZero ((RingedSpace.modulePullbackDerived g.left.toShHom).obj Q) →
          newtonClass g p = 0)
    (newtonClass_commute :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (g : Y ⟶ BivariantClass.GysinAtInfinity.compactification X b)
        [LocallyOfFiniteType g.left]
        {Y' : Over S} [LocallyOfFiniteType Y'.hom]
        (h : Y' ⟶ Y) [LocallyOfFiniteType h.left]
        (r : ℤ) (c : BivariantClass delta h r),
        BivariantClass.Commute delta h (𝟙 Y) c (newtonClass g p))
    (localized : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (p : ℤ))
    (hlocalized : IsInfinityLocalizedExtension delta i b t (p : ℤ)
      (newtonClass
        (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) ≫
          BivariantClass.GysinAtInfinity.infinityInclusion X b) p)
      localized)
    {Y : Over S} [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) [LocallyOfFiniteType f.left]
    (q : ℤ) (c : BivariantClass delta f q) :
    BivariantClass.Commute delta f
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) c
      (classAtZero delta i b (p : ℤ) localized) := sorry

/-- Lemma 42.49.5 (2): the Chern bivariant class at zero commutes with every
homogeneous bivariant class on a locally finite-type morphism into `X`. -/
@[stacks 0FAW]
theorem chernClassAtZero_commute
    {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ} [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (p : ℕ)
    (restrictionRank : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) 0 p)
    (chernClass :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (g : Y ⟶ BivariantClass.GysinAtInfinity.compactification X b)
        [LocallyOfFiniteType g.left] (r : ℕ),
        BivariantClass delta (𝟙 Y) (r : ℤ))
    (chernClass_naturality :
      ∀ {Y Y' : Over S} [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Y'.hom]
        (g : Y ⟶ BivariantClass.GysinAtInfinity.compactification X b)
        [LocallyOfFiniteType g.left] (h : Y' ⟶ Y) [LocallyOfFiniteType h.left] (r : ℕ),
        BivariantClass.restrict delta h (𝟙 Y') h IsPullback.of_id_snd
            (r : ℤ) (chernClass g r) =
          chernClass (h ≫ g) r)
    (chernClass_vanishes :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (g : Y ⟶ BivariantClass.GysinAtInfinity.compactification X b)
        [LocallyOfFiniteType g.left],
        Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
            ((RingedSpace.modulePullbackDerived g.left.toShHom).obj Q) 0 p →
          chernClass g p = 0)
    (chernClass_commute :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (g : Y ⟶ BivariantClass.GysinAtInfinity.compactification X b)
        [LocallyOfFiniteType g.left]
        {Y' : Over S} [LocallyOfFiniteType Y'.hom]
        (h : Y' ⟶ Y) [LocallyOfFiniteType h.left]
        (r : ℤ) (c : BivariantClass delta h r),
        BivariantClass.Commute delta h (𝟙 Y) c (chernClass g p))
    (localized : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (p : ℤ))
    (hlocalized : IsInfinityLocalizedExtension delta i b t (p : ℤ)
      (chernClass
        (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) ≫
          BivariantClass.GysinAtInfinity.infinityInclusion X b) p)
      localized)
    {Y : Over S} [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) [LocallyOfFiniteType f.left]
    (q : ℤ) (c : BivariantClass delta f q) :
    BivariantClass.Commute delta f
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) c
      (classAtZero delta i b (p : ℤ) localized) := sorry

end AlgebraicGeometry.LocalizedChern
