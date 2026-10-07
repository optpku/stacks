module

public import stacks_project.Chap42.Lemma_42_47_6
public import stacks_project.Chap42.Lemma_42_48_1

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- Lemma 42.49.1 (1): a perfect complex on a proper compactification that is trivial on
a closed part of the infinity fibre containing every point over `X \ Z` determines a
degree-`p` bivariant Newton class on `Z ⟶ X` whose proper pushforward is the Newton
class of the restriction to the zero fibre. -/
@[stacks 0F9K]
theorem existsNewtonClassAtZero
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
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
        [LocallyOfFiniteType g.left] (q : ℕ),
        BivariantClass δ (𝟙 Y) (q : ℤ))
    (newtonClass_naturality :
      ∀ {Y Y' : Over S} [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Y'.hom]
        (g : Y ⟶ BivariantClass.GysinAtInfinity.compactification X b)
        [LocallyOfFiniteType g.left] (h : Y' ⟶ Y) [LocallyOfFiniteType h.left] (q : ℕ),
        BivariantClass.restrict δ h (𝟙 Y') h IsPullback.of_id_snd
            (q : ℤ) (newtonClass g q) =
          newtonClass (h ≫ g) q)
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
        (q : ℤ) (c : BivariantClass δ h q),
        BivariantClass.Commute δ h (𝟙 Y) c (newtonClass g p)) :
    ∃ P' : BivariantClass δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ),
      BivariantClass.pushforwardToTarget δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) P' =
        newtonClass (BivariantClass.GysinAtInfinity.zeroSectionLift X b) p := sorry

/-- Lemma 42.49.1 (2): if the restriction to the closed part of the infinity fibre is a
degree-zero vector bundle of pointwise rank less than `p`, the corresponding construction
gives a degree-`p` bivariant Chern class on `Z ⟶ X` whose proper pushforward is the Chern
class of the restriction to the zero fibre. -/
@[stacks 0F9K]
theorem existsChernClassAtZero
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
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
        [LocallyOfFiniteType g.left] (q : ℕ),
        BivariantClass δ (𝟙 Y) (q : ℤ))
    (chernClass_naturality :
      ∀ {Y Y' : Over S} [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Y'.hom]
        (g : Y ⟶ BivariantClass.GysinAtInfinity.compactification X b)
        [LocallyOfFiniteType g.left] (h : Y' ⟶ Y) [LocallyOfFiniteType h.left] (q : ℕ),
        BivariantClass.restrict δ h (𝟙 Y') h IsPullback.of_id_snd
            (q : ℤ) (chernClass g q) =
          chernClass (h ≫ g) q)
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
        (q : ℤ) (c : BivariantClass δ h q),
        BivariantClass.Commute δ h (𝟙 Y) c (chernClass g p)) :
    ∃ c' : BivariantClass δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ),
      BivariantClass.pushforwardToTarget δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) c' =
        chernClass (BivariantClass.GysinAtInfinity.zeroSectionLift X b) p := sorry

end AlgebraicGeometry.LocalizedChern
