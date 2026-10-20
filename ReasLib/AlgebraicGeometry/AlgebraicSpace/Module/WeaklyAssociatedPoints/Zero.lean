/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Vanishing of algebraic space modules and weakly associated points

A quasi-coherent module on an algebraic space vanishes exactly when its weakly
associated locus is empty.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A quasi-coherent module on an algebraic space is zero if and only if its
weakly associated locus is empty. -/
@[stacks 0CU0]
theorem isZero_iff_weakAss_eq_empty {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] :
    IsZero F ↔ F.weakAss = (∅ : Set (Points X)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
