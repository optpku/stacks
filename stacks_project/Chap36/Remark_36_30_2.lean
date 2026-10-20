/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.ProperSupportFlatBaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Remark 36.30.2 (1): derived global sections of a finitely presented module that is flat
over an affine base and has proper support form a perfect derived module, hence admit a bounded
finite-projective complex model. -/
@[stacks 0A1I]
#check (AlgebraicGeometry.Scheme.Modules.affineGlobalSections_isPerfect_of_finitePresentation :
  ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [Scheme.Hom.FinitePresentation f]
    [Scheme.Modules.AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    (G : X.Modules) [G.IsFinitePresentation]
    [SheafOfModules.IsFlatOver G f.toShHom]
    [Scheme.Modules.HasProperSupportOver f G],
    DerivedCategory.IsPerfect
      (Scheme.Modules.affineBaseModuleDerivedGlobalSections A f G))

/- Remark 36.30.2 (2): for every affine base change `A → A'`, the canonical comparison
from scalar extension of derived global sections to the derived global sections of the
base-changed module is an isomorphism. -/
@[stacks 0A1I]
#check (AlgebraicGeometry.Scheme.Modules.affineGlobalSectionsBaseChange_isIso_of_finitePresentation :
  ∀ {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A'] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [Scheme.Hom.FinitePresentation f]
    [Scheme.Modules.AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
    [Scheme.Modules.AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    [Scheme.Modules.AffineBaseModuleDerivedAdjunction.HasPair A f]
    [Scheme.Modules.AffineBaseModuleDerivedAdjunction.HasLeftDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [Scheme.Modules.AffineBaseModuleDerivedAdjunction.HasRightDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [Scheme.Modules.AffineBaseModuleDerivedAdjunction.HasPair A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [Scheme.Modules.AffineBaseChangeDerivedCompatibility.HasScalarExtension A A']
    [Scheme.Modules.AffineBaseChangeDerivedCompatibility.HasPullback A A' f]
    [Scheme.Modules.AffineBaseChangeDerivedCompatibility.SourceRoute A A' f]
    [Scheme.Modules.AffineBaseChangeDerivedCompatibility.TargetRoute A A' f]
    (G : X.Modules) [G.IsFinitePresentation]
    [SheafOfModules.IsFlatOver G f.toShHom]
    [Scheme.Modules.HasProperSupportOver f G],
    IsIso (Scheme.Modules.affineBaseModuleDerivedGlobalSectionsBaseChangeMap A A' f G))
