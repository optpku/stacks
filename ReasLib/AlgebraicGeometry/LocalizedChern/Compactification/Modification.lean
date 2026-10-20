/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Compactification
public import ReasLib.AlgebraicGeometry.LocalizedChern.DerivedEnvelopeCaps.BaseChange
public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension.BaseChange
public import ReasLib.AlgebraicGeometry.BivariantClass.GysinAtInfinity.Modification

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- The localized Newton class of a perfect complex with envelope-defined Chern
operations is unchanged by derived pullback along a proper modification that is an
isomorphism over the affine part, for any admissible closed parts of infinity. -/
theorem newtonClassAtZero_eq_of_modification
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W W' T T' : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (g : W' ⟶ W) [IsProper g]
    [IsIso (g ∣_ (b ⁻¹ᵁ BivariantClass.GysinAtInfinity.affinePart X))]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
    (classes : ChernClass.Theory δ
      (BivariantClass.GysinAtInfinity.compactification X b).hom)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (t' : T' ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X (g ≫ b)).left)
    [IsClosedImmersion t']
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
        (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (containsComplement' :
      (BivariantClass.GysinAtInfinity.infinityToX X (g ≫ b)).left.base ⁻¹'
        (Set.range i.base)ᶜ ⊆ Set.range t'.base)
    (p : ℕ)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
    (restrictionZero' : IsZero
      ((RingedSpace.modulePullbackDerived
        (t' ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X (g ≫ b)).left).toShHom).obj
        ((RingedSpace.modulePullbackDerived g.toShHom).obj Q)))
    (output output' : BivariantClass δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (houtput : IsCompactificationLocalization δ i b t (p : ℤ)
      (EnvelopeCaps.derivedClass δ classes Q perfect defined false p) output)
    (houtput' : IsCompactificationLocalization δ i (g ≫ b) t' (p : ℤ)
      (EnvelopeCaps.derivedClass δ
        (classes.reanchor (BivariantClass.GysinAtInfinity.compactification X (g ≫ b)))
        ((RingedSpace.modulePullbackDerived g.toShHom).obj Q)
        (RingedSpace.modulePullbackDerived_isPerfect g.toShHom Q perfect)
        (EnvelopeCaps.defined_pullback g Q defined) false p) output') :
    output = output' := sorry

/-- The localized Chern class of a perfect complex with envelope-defined Chern
operations is unchanged by derived pullback along a proper modification that is an
isomorphism over the affine part, for any admissible closed parts of infinity. -/
theorem chernClassAtZero_eq_of_modification
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W W' T T' : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (g : W' ⟶ W) [IsProper g]
    [IsIso (g ∣_ (b ⁻¹ᵁ BivariantClass.GysinAtInfinity.affinePart X))]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
    (classes : ChernClass.Theory δ
      (BivariantClass.GysinAtInfinity.compactification X b).hom)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (t' : T' ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X (g ≫ b)).left)
    [IsClosedImmersion t']
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
        (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (containsComplement' :
      (BivariantClass.GysinAtInfinity.infinityToX X (g ≫ b)).left.base ⁻¹'
        (Set.range i.base)ᶜ ⊆ Set.range t'.base)
    (p : ℕ)
    (restrictionRank : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) 0 p)
    (restrictionRank' : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t' ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X (g ≫ b)).left).toShHom).obj
        ((RingedSpace.modulePullbackDerived g.toShHom).obj Q)) 0 p)
    (output output' : BivariantClass δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (houtput : IsCompactificationLocalization δ i b t (p : ℤ)
      (EnvelopeCaps.derivedClass δ classes Q perfect defined true p) output)
    (houtput' : IsCompactificationLocalization δ i (g ≫ b) t' (p : ℤ)
      (EnvelopeCaps.derivedClass δ
        (classes.reanchor (BivariantClass.GysinAtInfinity.compactification X (g ≫ b)))
        ((RingedSpace.modulePullbackDerived g.toShHom).obj Q)
        (RingedSpace.modulePullbackDerived_isPerfect g.toShHom Q perfect)
        (EnvelopeCaps.defined_pullback g Q defined) true p) output') :
    output = output' := sorry

end AlgebraicGeometry.LocalizedChern
