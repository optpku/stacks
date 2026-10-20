/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Characterization
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Characterization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.TorDimension.Affine

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.tilde

/-- Degreewise affine tilde sheafification preserves and reflects perfectness of a
cochain complex in the derived category. -/
theorem isPerfect_iff
    (A : CommRingCat.{u}) (M : CochainComplex (ModuleCat A) ℤ) :
    RingedSpace.ModuleDerived.IsPerfect
        (DerivedCategory.Q.obj
          (((AlgebraicGeometry.tilde.functor A).mapHomologicalComplex (up ℤ)).obj M)) ↔
      DerivedCategory.IsPerfect (DerivedCategory.Q.obj M) := sorry

end AlgebraicGeometry.tilde
