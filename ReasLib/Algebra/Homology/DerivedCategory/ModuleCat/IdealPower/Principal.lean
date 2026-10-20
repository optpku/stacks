/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.End.Power
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Quotient
public import ReasLib.Algebra.Module.Torsion.Stability
public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle
public import ReasLib.RingTheory.Ideal.Principal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal-power two-term towers

For `f : A`, this file specializes the categorical endomorphism-power tower to multiplication by
`f` on the regular `A`-module.  It also connects stabilization of the source's `f`-power torsion
submodules to the fixed-cutoff pro-isomorphism criterion.

@stack 091X
@stack 0923
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.PrincipalPower

variable {A : Type u} [CommRing A]

/-- Multiplication by `f` as an endomorphism of the regular `A`-module. -/
@[stacks 091X "principal multiplication endomorphism"]
noncomputable def mulEnd (f : A) : End (ModuleCat.of A A) :=
  ModuleCat.ofHom (LinearMap.mulRight A f)

/-- Powers of the multiplication endomorphism are multiplication by the corresponding powers of
`f`. -/
@[stacks 091X "principal multiplication power formula"]
theorem mulEnd_pow (f : A) (n : ℕ) :
    mulEnd f ^ n = ModuleCat.ofHom (LinearMap.mulRight A (f ^ n)) := sorry

/-- Stability of the source's `f`-power torsion stages gives stability of the categorical kernels
at the same zero-based cutoff. -/
@[stacks 091X "principal torsion stability as kernel stability"]
theorem kernelStableAt_of_isPowerTorsionStableAt (f : A) (c : ℕ)
    (h : Module.IsPowerTorsionStableAt A A f c) :
    CategoryTheory.End.Power.kernelStableAt (mulEnd f) c := sorry

/-- The categorical cokernel stage is the module `A ⧸ (f^(n+1))`, up to the canonical notion of
isomorphism for a chosen cokernel. -/
@[stacks 091X "principal power cokernel stage"]
theorem quotientStage_isIsomorphic (f : A) (n : ℕ) :
    IsIsomorphic (CategoryTheory.End.Power.quotientStage (mulEnd f) n)
      (ModuleCat.of A (A ⧸ principalPowerIdeal f (n + 1))) := sorry

/-- After placing both modules in degree zero, the derived cokernel stage is the explicit
principal-power quotient stage. -/
@[stacks 091X "derived principal power cokernel stage"]
theorem cokernelStage_isIsomorphic (f : A) (n : ℕ) :
    IsIsomorphic (CategoryTheory.End.Power.cokernelStage (mulEnd f) n)
      (ModuleCat.single0 (ModuleCat.of A (A ⧸ principalPowerIdeal f (n + 1)))) := sorry

/-- The derived categorical cokernel tower is the explicit principal ideal-power quotient tower,
up to isomorphism of sequential inverse systems. -/
@[stacks 091X "principal power cokernel tower"]
theorem cokernelSystem_isIsomorphic (f : A) :
    IsIsomorphic (CategoryTheory.End.Power.cokernelSystem (mulEnd f))
      (CategoryTheory.DerivedCategory.IdealPower.system (principalIdeal f)) := sorry

/-- The two-term principal-power tower after derived tensoring with a fixed complex `K`. -/
@[stacks 0923 "principal two-term derived tensor tower"]
abbrev twoTermTensorSystem (f : A) (K : DerivedCategory (ModuleCat A)) :
    SequentialInverseSystem (DerivedCategory (ModuleCat A)) :=
  CategoryTheory.End.Power.twoTermSystem (mulEnd f) ⋙
    DerivedCategory.derivedTensorProduct K

/-- The principal-power cokernel tower after derived tensoring with a fixed complex `K`. -/
@[stacks 0923 "principal quotient derived tensor tower"]
abbrev cokernelTensorSystem (f : A) (K : DerivedCategory (ModuleCat A)) :
    SequentialInverseSystem (DerivedCategory (ModuleCat A)) :=
  CategoryTheory.End.Power.cokernelSystem (mulEnd f) ⋙
    DerivedCategory.derivedTensorProduct K

/-- The stagewise two-term-to-cokernel augmentation after derived tensoring with `K`. -/
@[stacks 0923 "principal completion tower comparison"]
abbrev tensorAugmentationSystem (f : A) (K : DerivedCategory (ModuleCat A)) :
    twoTermTensorSystem f K ⟶ cokernelTensorSystem f K :=
  Functor.whiskerRight
    (CategoryTheory.End.Power.augmentationSystem (mulEnd f))
    (DerivedCategory.derivedTensorProduct K)

/-- Lemma 15.94.2 (Stacks `0923`): suppose two endofunctors are objectwise derived limits of
the principal two-term and quotient towers, and a natural transformation between them induces
the canonical augmentation at every stage. That comparison is an isomorphism exactly when the
`f`-power torsion of `A` is bounded at some positive cutoff. -/
@[stacks 0923]
theorem completionComparison_isIso_iff (f : A)
    (twoTermCompletion quotientCompletion :
      DerivedCategory (ModuleCat A) ⥤ DerivedCategory (ModuleCat A))
    (comparison : twoTermCompletion ⟶ quotientCompletion)
    (hTwoTerm : ∀ K, CategoryTheory.IsDerivedLimit
      (twoTermTensorSystem f K) (twoTermCompletion.obj K))
    (hQuotient : ∀ K, CategoryTheory.IsDerivedLimit
      (cokernelTensorSystem f K) (quotientCompletion.obj K))
    (hcomparison : ∀ (K : DerivedCategory (ModuleCat A)) (n : ℕ),
      comparison.app K ≫ (hQuotient K).stageProjection n =
        (hTwoTerm K).stageProjection n ≫
          (tensorAugmentationSystem f K).app (op n)) :
    IsIso comparison ↔
      ∃ c : ℕ+, Module.IsPowerTorsionStableAt A A f c := sorry

/-- Lemma 15.94.1 (1) (Stacks `091X`): at a positive cutoff where `f`-power torsion is bounded,
the maps `A ⧸ (f^(n+c)) ⟶ [A --f^n--> A]` assemble into a shift inverse to the canonical
two-term-to-quotient augmentation. -/
@[stacks 091X]
theorem existsShiftInverse (f : A) (c : ℕ+)
    (h : Module.IsPowerTorsionStableAt A A f c) :
    ∃ reverse :
        SequentialInverseSystem.shift
            (CategoryTheory.End.Power.cokernelSystem (mulEnd f)) c ⟶
          CategoryTheory.End.Power.twoTermSystem (mulEnd f),
      Pro.SequentialHom.IsShiftInverse
        (CategoryTheory.End.Power.augmentationSystem (mulEnd f)) c reverse := sorry

/-- Lemma 15.94.1 (2) (Stacks `091X`): bounded `f`-power torsion makes the canonical maps
`[A --f^n--> A] ⟶ A ⧸ (f^n)` an isomorphism of sequential pro-objects. -/
@[stacks 091X]
theorem augmentation_isIso (f : A) (c : ℕ+)
    (h : Module.IsPowerTorsionStableAt A A f c) :
    IsIso
      (Pro.SequentialHom.ofNatTrans
        (CategoryTheory.End.Power.augmentationSystem (mulEnd f))).toHom := sorry

/-- Lemma 15.94.1 (3) (Stacks `091X`): over a Noetherian ring, principal power torsion is
bounded at some positive cutoff. -/
@[stacks 091X]
theorem existsStableCutoff_of_isNoetherian [IsNoetherianRing A] (f : A) :
    ∃ c : ℕ+, Module.IsPowerTorsionStableAt A A f c := sorry

end CategoryTheory.DerivedCategory.PrincipalPower
