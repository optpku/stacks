/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
import Mathlib.Tactic.CrossRefAttribute

/-!
# Scheme-theoretic density in fibers of finite-type morphisms

This file relates scheme-theoretic density in the generic fiber to density in the fibers over an
open subscheme of an irreducible target.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteType

/-- If an open subscheme is scheme-theoretically dense in the generic fiber of a finite-type
morphism to an irreducible scheme, it is scheme-theoretically dense in every fiber over some
nonempty open subscheme of the target. -/
@[stacks 0573]
theorem exists_open_schemeTheoreticallyDense_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y]
    (U : X.Opens)
    (hη : schemeTheoreticallyDense ((f.fiberι (genericPoint Y)) ⁻¹ᵁ U)) :
    ∃ V : Y.Opens, Nonempty V ∧
      ∀ y : Y, y ∈ V → schemeTheoreticallyDense ((f.fiberι y) ⁻¹ᵁ U) := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteType
