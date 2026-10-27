/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover.WhitneySum

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open ChernClass.Derived
open RingedSpace.ModuleDerived
open BivariantClass.Cutoff
open ChowCohomology.Nonnegative.Completion

/- Lemma 42.47.8: the cutoff total Chern series of a biproduct is the
sum-cutoff product of the two cutoff total Chern series, with ambient coefficients
below the cutoff and the localized extensions of Lemma 42.47.1 at and above it.

Source correction (0FAL): hypothesis (2) requires the restrictions to `X₁`,
not merely to `X₁ ∩ X₂`, to be degree-zero finite locally free modules of ranks
strictly less than `p` and `q`. The product includes every nonnegative coefficient,
using proper pushforward of relative inputs below the output cutoff. -/
@[stacks 0FAL] #check (AlgebraicGeometry.LocalizedChern.cutoffChernClass_biprod :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ}
    [IsDimensionFunction δ] {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}} (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (E F : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfectE : RingedSpace.ModuleDerived.IsPerfect E)
    (perfectF : RingedSpace.ModuleDerived.IsPerfect F)
    (definedE : ChernClass.Derived.IsDefined E)
    (definedF : ChernClass.Derived.IsDefined F) (p q : ℕ)
    (rankE : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived i₁.toShHom).obj E) 0 p)
    (rankF : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived i₁.toShHom).obj F) 0 q)
    (classes : ChernClass.Theory δ X.hom)
    (localizedE localizedF localizedBiprod :
      (k : ℕ) → BivariantClass δ
        (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) (k : ℤ))
    (hlocalizedE : ∀ k : ℕ, p ≤ k →
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (k : ℤ)
        (totalClass δ (i₂ ≫ X.hom) (classes.reanchor (Over.mk (i₂ ≫ X.hom)))
          ((RingedSpace.modulePullbackDerived i₂.toShHom).obj E)
          (RingedSpace.modulePullbackDerived_isPerfect i₂.toShHom E perfectE)
          (IsDefined.pullback i₂ definedE) k)
        (localizedE k))
    (hlocalizedF : ∀ k : ℕ, q ≤ k →
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (k : ℤ)
        (totalClass δ (i₂ ≫ X.hom) (classes.reanchor (Over.mk (i₂ ≫ X.hom)))
          ((RingedSpace.modulePullbackDerived i₂.toShHom).obj F)
          (RingedSpace.modulePullbackDerived_isPerfect i₂.toShHom F perfectF)
          (IsDefined.pullback i₂ definedF) k)
        (localizedF k))
    (hlocalizedBiprod : ∀ k : ℕ, p + q ≤ k →
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (k : ℤ)
        (totalClass δ (i₂ ≫ X.hom) (classes.reanchor (Over.mk (i₂ ≫ X.hom)))
          ((RingedSpace.modulePullbackDerived i₂.toShHom).obj (E ⊞ F))
          (RingedSpace.modulePullbackDerived_isPerfect i₂.toShHom (E ⊞ F)
            (perfectE.biprod perfectF))
          (IsDefined.pullback i₂ (definedE.biprod definedF)) k)
        (localizedBiprod k)),
    (fun n ↦ cutoffChernClass δ
      (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) (p + q) n
      (totalClass δ X.hom classes (E ⊞ F)
        (perfectE.biprod perfectF) (definedE.biprod definedF) n)
      (localizedBiprod n)) =
      familyMul δ (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) p q
        (fun i ↦ cutoffChernClass δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) p i
          (totalClass δ X.hom classes E perfectE definedE i) (localizedE i))
        (fun j ↦ cutoffChernClass δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) q j
          (totalClass δ X.hom classes F perfectF definedF j) (localizedF j)))

end AlgebraicGeometry.LocalizedChern
