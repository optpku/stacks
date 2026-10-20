/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Compactification
public import ReasLib.AlgebraicGeometry.BivariantClass.Commutation
public import ReasLib.AlgebraicGeometry.Scheme.Over.ClosedImmersion

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- A compactification-localized bivariant class commutes with a homogeneous
class when its ambient identity class commutes universally. -/
theorem isCompactificationLocalization_commute
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t] (p : ℤ)
    (ambient : BivariantClass delta
      (𝟙 (BivariantClass.GysinAtInfinity.compactification X b)) p)
    (output : BivariantClass delta
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p)
    (houtput : IsCompactificationLocalization delta i b t p ambient output)
    (ambient_commute :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (g : Y ⟶ BivariantClass.GysinAtInfinity.compactification X b)
        [LocallyOfFiniteType g.left]
        (q : ℤ) (c : BivariantClass delta g q),
        BivariantClass.Commute delta g
          (𝟙 (BivariantClass.GysinAtInfinity.compactification X b)) c ambient)
    {Y : Over S} [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) [LocallyOfFiniteType f.left]
    (q : ℤ) (c : BivariantClass delta f q) :
    BivariantClass.Commute delta f
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) c output := sorry

/-- The localized Newton class at zero commutes with every homogeneous bivariant
class on a locally finite-type morphism into `X`. -/
theorem newtonClassAtZero_commute
    {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ}
    [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
    (classes : ChernClass.Theory delta
      (BivariantClass.GysinAtInfinity.compactification X b).hom)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (p : ℕ)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
    (output : BivariantClass delta
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (houtput : IsCompactificationLocalization delta i b t (p : ℤ)
      (EnvelopeCaps.derivedClass delta classes Q perfect defined false p) output)
    {Y : Over S} [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) [LocallyOfFiniteType f.left]
    (q : ℤ) (c : BivariantClass delta f q) :
    BivariantClass.Commute delta f
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) c output := sorry

/-- The localized Chern class at zero commutes with every homogeneous bivariant
class on a locally finite-type morphism into `X`. -/
theorem chernClassAtZero_commute
    {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ}
    [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ W), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
    (classes : ChernClass.Theory delta
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
    (output : BivariantClass delta
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (houtput : IsCompactificationLocalization delta i b t (p : ℤ)
      (EnvelopeCaps.derivedClass delta classes Q perfect defined true p) output)
    {Y : Over S} [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) [LocallyOfFiniteType f.left]
    (q : ℤ) (c : BivariantClass delta f q) :
    BivariantClass.Commute delta f
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) c output := sorry

end AlgebraicGeometry.LocalizedChern
