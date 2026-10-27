/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocalizedChern.Compactification.WhitneySum

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Lemma 42.49.7: the complete compactification-localized cutoff Chern family of
Q ⊞ Q' equals the sum-cutoff product of the families of Q and Q', when their restrictions
to the specified closed part of infinity have ranks strictly below p and p'. -/
@[stacks 0FAY] #check
  (AlgebraicGeometry.LocalizedChern.cutoffChernClassAtZero_biprod :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ}
    [IsDimensionFunction δ] {X : Over S} [LocallyOfFiniteType X.hom]
    {Z W T : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q Q' : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfectQ : RingedSpace.ModuleDerived.IsPerfect Q)
    (perfectQ' : RingedSpace.ModuleDerived.IsPerfect Q')
    (definedQ : ChernClass.Derived.IsDefined Q)
    (definedQ' : ChernClass.Derived.IsDefined Q')
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (p p' : ℕ)
    (restrictionRankQ : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj
        Q) 0 p)
    (restrictionRankQ' : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj
        Q') 0 p')
    (classes : ChernClass.Theory δ
      (BivariantClass.GysinAtInfinity.compactification X b).hom)
    (localizedQ localizedQ' localizedBiprod :
      (n : ℕ) → BivariantClass δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (n : ℤ))
    (hlocalizedQ : ∀ n : ℕ, p ≤ n →
      IsCompactificationLocalization δ i b t (n : ℤ)
        (EnvelopeCaps.derivedClass δ classes Q perfectQ definedQ true n) (localizedQ n))
    (hlocalizedQ' : ∀ n : ℕ, p' ≤ n →
      IsCompactificationLocalization δ i b t (n : ℤ)
        (EnvelopeCaps.derivedClass δ classes Q' perfectQ' definedQ' true n) (localizedQ' n))
    (hlocalizedBiprod : ∀ n : ℕ, p + p' ≤ n →
      IsCompactificationLocalization δ i b t (n : ℤ)
        (EnvelopeCaps.derivedClass δ classes (Q ⊞ Q')
          (perfectQ.biprod perfectQ') (definedQ.biprod definedQ') true n)
        (localizedBiprod n)),
    -- Local instance justification (defeq pin): expose the existing closed-immersion hypothesis through the Over.homMk projection for cutoff constructors and convolution.
    letI : IsClosedImmersion (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X).left :=
      inferInstanceAs (IsClosedImmersion i);
    (fun n ↦ cutoffChernClass δ
      (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) (p + p') n
      (BivariantClass.restrict δ
        (BivariantClass.GysinAtInfinity.zeroSectionLift X b) (𝟙 X)
        (BivariantClass.GysinAtInfinity.zeroSectionLift X b) IsPullback.of_id_snd (n : ℤ)
        (EnvelopeCaps.derivedClass δ classes (Q ⊞ Q')
          (perfectQ.biprod perfectQ') (definedQ.biprod definedQ') true n))
      (localizedBiprod n)) =
      BivariantClass.Cutoff.familyMul δ
        (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) p p'
        (fun n ↦ cutoffChernClass δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) p n
          (BivariantClass.restrict δ
            (BivariantClass.GysinAtInfinity.zeroSectionLift X b) (𝟙 X)
            (BivariantClass.GysinAtInfinity.zeroSectionLift X b) IsPullback.of_id_snd (n : ℤ)
            (EnvelopeCaps.derivedClass δ classes Q perfectQ definedQ true n))
          (localizedQ n))
        (fun n ↦ cutoffChernClass δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) p' n
          (BivariantClass.restrict δ
            (BivariantClass.GysinAtInfinity.zeroSectionLift X b) (𝟙 X)
            (BivariantClass.GysinAtInfinity.zeroSectionLift X b) IsPullback.of_id_snd (n : ℤ)
            (EnvelopeCaps.derivedClass δ classes Q' perfectQ' definedQ' true n))
          (localizedQ' n)))

end AlgebraicGeometry.LocalizedChern
