/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

/-!
# The affine-line involution quotient sheaf

The quotient of the affine line by its punctured negation relation is the fppf
sheafification of the corresponding quotient presheaf.
-/

@[expose] public section

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.sheafOfPoints :
    ∀ (k : Type u) [Field k], CategoryTheory.Sheaf
      (AlgebraicGeometry.Scheme.fppfTopology.over
        (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.base k)) (Type (u + 1)))
