/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.DerivedBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.Tensor

/-!
# Proper-support flat base change for module cohomology

This file records perfectness and arbitrary affine base change for the derived global sections
of finitely presented modules that are flat over an affine base and have proper support.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Derived global sections of a finitely presented module that is flat over an affine base
and has proper support form a perfect derived module. -/
theorem affineGlobalSections_isPerfect_of_finitePresentation
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [Scheme.Hom.FinitePresentation f]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    (G : X.Modules) [G.IsFinitePresentation]
    [SheafOfModules.IsFlatOver G f.toShHom]
    [Scheme.Modules.HasProperSupportOver f G] :
    DerivedCategory.IsPerfect (affineBaseModuleDerivedGlobalSections A f G) := sorry

/-- After any affine base change, the canonical comparison from scalar extension of derived
global sections to the derived global sections of the base-changed module is an isomorphism. -/
@[instance]
theorem affineGlobalSectionsBaseChange_isIso_of_finitePresentation
    {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A'] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [Scheme.Hom.FinitePresentation f]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasPair A f]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseModuleDerivedAdjunction.HasPair A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseChangeDerivedCompatibility.HasScalarExtension A A']
    [AffineBaseChangeDerivedCompatibility.HasPullback A A' f]
    [AffineBaseChangeDerivedCompatibility.SourceRoute A A' f]
    [AffineBaseChangeDerivedCompatibility.TargetRoute A A' f]
    (G : X.Modules) [G.IsFinitePresentation]
    [SheafOfModules.IsFlatOver G f.toShHom]
    [Scheme.Modules.HasProperSupportOver f G] :
    IsIso (affineBaseModuleDerivedGlobalSectionsBaseChangeMap A A' f G) := sorry

end AlgebraicGeometry.Scheme.Modules
