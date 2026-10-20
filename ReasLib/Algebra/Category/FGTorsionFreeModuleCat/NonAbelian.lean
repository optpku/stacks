/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.FGTorsionFreeModuleCat.Kernels
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.CategoryTheory.Abelian.Images

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace FGTorsionFreeModuleCat

/-- Multiplication by two on the finitely generated torsion-free integer module. -/
def mulTwo : of ℤ ℤ ⟶ of ℤ ℤ :=
  ofHom (LinearMap.mulLeft ℤ (2 : ℤ))

/-- The canonical coimage-to-image comparison for multiplication by two on the integer module
 is not an isomorphism in the category of finitely generated torsion-free modules. -/
theorem mulTwo_coimageImageComparison_not_isIso :
    ¬ IsIso (Abelian.coimageImageComparison mulTwo) :=
  sorry

end FGTorsionFreeModuleCat
