module

public import stacks_project.Chap42.Lemma_42_49_1
public import stacks_project.Chap42.Lemma_42_48_4

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- Lemma 42.49.4 (1): composition of the Gysin-at-infinity class with the Chern
class on the zero fibre agrees with its composition with the pushforward of the
localized Chern class. -/
@[stacks 0FAV]
theorem gysinAtInfinity_comp_chernClassAtZero
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
        BivariantClass.Commute δ h (𝟙 Y) c (chernClass g p))
    (c' : BivariantClass δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (pushforward_eq :
      BivariantClass.pushforwardToTarget δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) c' =
        chernClass (BivariantClass.GysinAtInfinity.zeroSectionLift X b) p) :
    BivariantClass.comp δ
        (BivariantClass.GysinAtInfinity.infinityToX X b) (𝟙 (Over.mk X.hom))
        (BivariantClass.gysinAtInfinity δ X b)
        (chernClass (BivariantClass.GysinAtInfinity.zeroSectionLift X b) p) =
      BivariantClass.comp δ
        (BivariantClass.GysinAtInfinity.infinityToX X b) (𝟙 (Over.mk X.hom))
        (BivariantClass.gysinAtInfinity δ X b)
        (BivariantClass.pushforwardToTarget δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) c') := sorry

/-- Lemma 42.49.4 (2): composition of the Gysin-at-infinity class with the
pushforward of the localized Chern class agrees, up to the canonical index
transport, with composition by the Chern class on the infinity fibre. -/
@[stacks 0FAV]
theorem gysinAtInfinity_comp_localizedChernPushforward
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
        BivariantClass.Commute δ h (𝟙 Y) c (chernClass g p))
    (c' : BivariantClass δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (pushforward_eq :
      BivariantClass.pushforwardToTarget δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) c' =
        chernClass (BivariantClass.GysinAtInfinity.zeroSectionLift X b) p) :
    HEq
      (BivariantClass.comp δ
        (BivariantClass.GysinAtInfinity.infinityToX X b) (𝟙 (Over.mk X.hom))
        (BivariantClass.gysinAtInfinity δ X b)
        (BivariantClass.pushforwardToTarget δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) c'))
      (BivariantClass.comp δ
        (𝟙 (BivariantClass.GysinAtInfinity.infinityFiber X b))
        (BivariantClass.GysinAtInfinity.infinityToX X b)
        (chernClass (BivariantClass.GysinAtInfinity.infinityInclusion X b) p)
        (BivariantClass.gysinAtInfinity δ X b)) := sorry

end AlgebraicGeometry.LocalizedChern
