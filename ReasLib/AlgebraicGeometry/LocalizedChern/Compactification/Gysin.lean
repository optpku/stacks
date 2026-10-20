module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Compactification

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- For a perfect complex with envelope-defined Chern classes whose restriction to the
specified closed part of infinity is a degree-zero vector bundle of rank below `p`,
Gysin at infinity composed with the zero-fibre Chern class equals its composition with
the localized Chern pushforward, and also the infinity-fibre Chern class composed with
Gysin at infinity. -/
theorem gysinAtInfinity_comp_localizedChernPushforward
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
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
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) 0 p)
    (c' : BivariantClass δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (houtput : IsCompactificationLocalization δ i b t (p : ℤ)
      (EnvelopeCaps.derivedClass δ classes Q perfect defined true p) c') :
    let ambient := EnvelopeCaps.derivedClass δ classes Q perfect defined true p
    let atZero := BivariantClass.restrict δ
      (BivariantClass.GysinAtInfinity.zeroSectionLift X b) (𝟙 X)
      (BivariantClass.GysinAtInfinity.zeroSectionLift X b)
      IsPullback.of_id_snd (p : ℤ) ambient
    let atInfinity := BivariantClass.restrict δ
      (BivariantClass.GysinAtInfinity.infinityInclusion X b)
      (𝟙 (BivariantClass.GysinAtInfinity.infinityFiber X b))
      (BivariantClass.GysinAtInfinity.infinityInclusion X b)
      IsPullback.of_id_snd (p : ℤ) ambient
    let C := BivariantClass.gysinAtInfinity δ X b
    let f := BivariantClass.GysinAtInfinity.infinityToX X b
    let pushed := BivariantClass.properPushforwardToTarget δ
      (Over.homMk i (w := Eq.refl (i ≫ X.hom)) :
        Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom) (p : ℤ) c'
    (BivariantClass.comp δ f (𝟙 X) C atZero =
      BivariantClass.comp δ f (𝟙 X) C pushed) ∧
      HEq (BivariantClass.comp δ f (𝟙 X) C pushed)
        (BivariantClass.comp δ
          (𝟙 (BivariantClass.GysinAtInfinity.infinityFiber X b)) f atInfinity C) := sorry

end AlgebraicGeometry.LocalizedChern
