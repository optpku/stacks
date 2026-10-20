module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocalizedChern.Compactification

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Lemma 42.49.1 (1): a perfect complex with defined Chern classes on a proper
compactification, trivial on the specified part of infinity, has a canonical localized
Newton class whose proper pushforward is its Newton class on the zero fibre. -/
@[stacks 0F9K] #check
  (AlgebraicGeometry.LocalizedChern.existsNewtonClassAtZero :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
      {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
      (i : Z ⟶ X.left) [IsClosedImmersion i]
      (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
      [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
      (Q : RingedSpace.ModuleDerived W.toRingedSpace)
      (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
      (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
        RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
          ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
      (classes : ChernClass.Theory δ
        (BivariantClass.GysinAtInfinity.compactification X b).hom)
      (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
      [IsClosedImmersion t]
      (containsComplement :
        (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
            (Set.range i.base)ᶜ ⊆ Set.range t.base)
      (p : ℕ)
      (restrictionZero : IsZero
        ((RingedSpace.modulePullbackDerived
          (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q)),
      ∃ P' : BivariantClass δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ),
        IsCompactificationLocalization δ i b t (p : ℤ)
            (EnvelopeCaps.derivedClass δ classes Q perfect defined false p) P' ∧
          BivariantClass.properPushforwardToTarget δ
              (Over.homMk i (w := Eq.refl (i ≫ X.hom)) :
                Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom) (p : ℤ) P' =
            BivariantClass.restrict δ
              (BivariantClass.GysinAtInfinity.zeroSectionLift X b) (𝟙 X)
              (BivariantClass.GysinAtInfinity.zeroSectionLift X b)
              IsPullback.of_id_snd (p : ℤ)
              (EnvelopeCaps.derivedClass δ classes Q perfect defined false p))

/- Lemma 42.49.1 (2): a perfect complex with defined Chern classes on a proper
compactification, of degree-zero rank below `p` on the specified part of infinity, has a
canonical localized Chern class whose proper pushforward is its Chern class on the zero
fibre. -/
@[stacks 0F9K] #check
  (AlgebraicGeometry.LocalizedChern.existsChernClassAtZero :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
      {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
      (i : Z ⟶ X.left) [IsClosedImmersion i]
      (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
      [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
      (Q : RingedSpace.ModuleDerived W.toRingedSpace)
      (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
      (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
        RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
          ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
      (classes : ChernClass.Theory δ
        (BivariantClass.GysinAtInfinity.compactification X b).hom)
      (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
      [IsClosedImmersion t]
      (containsComplement :
        (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
            (Set.range i.base)ᶜ ⊆ Set.range t.base)
      (p : ℕ)
      (restrictionRank : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
        ((RingedSpace.modulePullbackDerived
          (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q)
          0 p),
      ∃ c' : BivariantClass δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ),
        IsCompactificationLocalization δ i b t (p : ℤ)
            (EnvelopeCaps.derivedClass δ classes Q perfect defined true p) c' ∧
          BivariantClass.properPushforwardToTarget δ
              (Over.homMk i (w := Eq.refl (i ≫ X.hom)) :
                Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom) (p : ℤ) c' =
            BivariantClass.restrict δ
              (BivariantClass.GysinAtInfinity.zeroSectionLift X b) (𝟙 X)
              (BivariantClass.GysinAtInfinity.zeroSectionLift X b)
              IsPullback.of_id_snd (p : ℤ)
              (EnvelopeCaps.derivedClass δ classes Q perfect defined true p))

end AlgebraicGeometry.LocalizedChern
