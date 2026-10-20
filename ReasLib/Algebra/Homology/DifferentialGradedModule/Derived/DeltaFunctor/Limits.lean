/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.DeltaFunctor
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coproducts and the DG-Module Delta Functor

The canonical delta functor from right differential graded modules to their derived category
inherits coproduct preservation from its underlying `fromModules` functor.  This named instance
bridges the opaque structure projection for downstream generic delta-functor constructions.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGradedModule.Derived.Delta

variable {R : Type u} [CommRing R]

/-- The canonical DG-module delta functor preserves coproducts of every available shape. -/
@[stacks 09L0 "the canonical DG-module delta functor preserves coproducts"]
instance functorPreservesCoproducts
    (A : CochainDGAlgebra.{u, max v w} R) (J : Type v) :
    PreservesColimitsOfShape (Discrete J) (functor A).toFunctor := sorry

end DifferentialGradedModule.Derived.Delta
