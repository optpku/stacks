/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.SheafyTrace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RestrictToScheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal

/-!
# Failure of the uncoherated sheafy trace

The canonical sheafy trace on the affine line over the integers need not be an
isomorphism before applying the quasicoherent coherator.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.MonoidalClosed

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- On the affine line over `Spec ℤ`, with transported structure sheaves as inputs,
the canonical uncoherated sheafy trace is not an isomorphism. -/
theorem affineLineSheafyTrace_not_iso :
    let YSch := Spec (CommRingCat.of ℤ)
    let XSch := Spec (CommRingCat.of (Polynomial ℤ))
    let fSch := Spec.map (CommRingCat.ofHom Polynomial.C)
    let Y := ofOver (Over.mk (𝟙 YSch))
    let X := ofOver (Over.mk fSch)
    let f := ofOverHomMk fSch (Category.comp_id fSch)
    let L := (schemeToSpaceDerived (Over.mk fSch)).obj
      (Scheme.DerivedQCoh.structureSheaf XSch)
    let K := (schemeToSpaceDerived (Over.mk (𝟙 YSch))).obj
      (Scheme.DerivedQCoh.structureSheaf YSch)
    ∀ [QuasiCompact f] [QuasiSeparated f]
      [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
      [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
      [BraidedCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived Y)]
      (tensorModelX : CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model
        (C := Modules X))
      (tensorModelY : CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model
        (C := Modules Y))
      [ModuleDerived.HasDerivedAdjunction f]
      [Functor.Monoidal (ModuleDerived.pullback f)]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a),
      ¬ IsIso (sheafyTraceMap f a adj L K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
