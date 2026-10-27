/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Regular
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian

/-!
# Nonzero meromorphic sections on integral algebraic spaces

For an invertible module on a locally Noetherian integral algebraic space,
regular meromorphic sections are exactly the nonzero meromorphic sections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A meromorphic section of an invertible module on a locally Noetherian
integral algebraic space is regular if and only if it is nonzero. -/
theorem isRegularMeromorphicSection_iff_ne_zero {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules) [isInvertibleObject L] (s : meromorphicSections X L) :
    IsRegularMeromorphicSection X L s ↔ s ≠ 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
