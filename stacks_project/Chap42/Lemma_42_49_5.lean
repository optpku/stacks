module

import StacksCheckRecall
public import stacks_project.Chap42.Lemma_42_49_1
public import stacks_project.Chap42.Lemma_42_49_5_Commutation
public import ReasLib.AlgebraicGeometry.LocalizedChern.Compactification.Commutation

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Lemma 42.49.5 (1): the localized Newton bivariant class at zero commutes
with every homogeneous bivariant class on a locally finite-type morphism into X. -/
@[stacks 0FAW] #check
  (AlgebraicGeometry.LocalizedChern.newtonClassAtZero_commute :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ}
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
      (q : ℤ) (c : BivariantClass delta f q),
      BivariantClass.Commute delta f
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) c output)

/- Lemma 42.49.5 (2): the localized Chern bivariant class at zero commutes
with every homogeneous bivariant class on a locally finite-type morphism into X. -/
@[stacks 0FAW] #check
  (AlgebraicGeometry.LocalizedChern.chernClassAtZero_commute :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ}
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
      (q : ℤ) (c : BivariantClass delta f q),
      BivariantClass.Commute delta f
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) c output)

end AlgebraicGeometry.LocalizedChern
