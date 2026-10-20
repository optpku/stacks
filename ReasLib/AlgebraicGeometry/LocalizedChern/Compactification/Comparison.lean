/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Compactification
public import ReasLib.AlgebraicGeometry.LocalizedChern.Classes

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- For a proper compactification that is an isomorphism over the affine-line part,
a perfect complex agreeing there with the pullback of a perfect complex vanishing off
the closed center has compactification-localized Newton class equal to the canonical
localized Newton class, provided both complexes satisfy the technical finiteness
condition and the required vanishing holds on the chosen closed part of infinity. -/
theorem newtonClassAtZero_eq_newtonClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (qPerfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (qDefined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
        (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (F : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect F)
    (vanishing : IsZero (restrictAway i F)) (p : ℕ)
    (finiteness : TechnicalCondition X F)
    (qFiniteness : TechnicalCondition
      (BivariantClass.GysinAtInfinity.compactification X b) Q)
    (affineAgreement : IsIsomorphic
      ((RingedSpace.modulePullbackDerived
        (b ⁻¹ᵁ BivariantClass.GysinAtInfinity.affinePart X).ι.toShHom).obj Q)
      ((RingedSpace.modulePullbackDerived (affineDeformationProjection b).toShHom).obj F))
    (restrictionOnT : RestrictionCondition
      (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left) Q p .vanishing)
    (output : BivariantClass δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (houtput : IsCompactificationLocalization δ i b t (p : ℤ)
      (EnvelopeCaps.derivedClass δ
        (classes.reanchor (BivariantClass.GysinAtInfinity.compactification X b))
        Q qPerfect qDefined false p) output) :
    output = newtonClass i classes F perfect vanishing finiteness p := sorry

/-- For a proper compactification that is an isomorphism over the affine-line part,
a perfect complex agreeing there with the pullback of a perfect complex whose restriction
off the closed center is a degree-zero vector bundle of rank below `p` has
compactification-localized Chern class equal to the canonical localized Chern class,
provided both complexes satisfy the technical finiteness condition and the same rank
bound holds on the chosen closed part of infinity. -/
theorem chernClassAtZero_eq_chernClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (qPerfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (qDefined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
        (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (F : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect F)
    (p : ℕ)
    (rankBound : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i F) 0 p)
    (finiteness : TechnicalCondition X F)
    (qFiniteness : TechnicalCondition
      (BivariantClass.GysinAtInfinity.compactification X b) Q)
    (affineAgreement : IsIsomorphic
      ((RingedSpace.modulePullbackDerived
        (b ⁻¹ᵁ BivariantClass.GysinAtInfinity.affinePart X).ι.toShHom).obj Q)
      ((RingedSpace.modulePullbackDerived (affineDeformationProjection b).toShHom).obj F))
    (restrictionOnT : RestrictionCondition
      (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left) Q p .rankBound)
    (output : BivariantClass δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (houtput : IsCompactificationLocalization δ i b t (p : ℤ)
      (EnvelopeCaps.derivedClass δ
        (classes.reanchor (BivariantClass.GysinAtInfinity.compactification X b))
        Q qPerfect qDefined true p) output) :
    output = chernClass i classes F perfect p rankBound finiteness := sorry

end AlgebraicGeometry.LocalizedChern
