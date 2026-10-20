/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-separatedness of a doubled-open gluing
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.DoubleAlong

variable {X : Scheme.{u}} (U : X.Opens)

/-- The fold from two copies of `X` glued along `U` is quasi-separated exactly when the open
immersion `U.toScheme ⟶ X` is quasi-compact. -/
@[stacks 01KL]
theorem fold_quasiSeparated_iff :
    QuasiSeparated (fold U) ↔ QuasiCompact U.ι := sorry

/-- A non-quasi-compact common open makes the fold from the doubled scheme non-quasi-separated. -/
@[stacks 01KL "non-quasi-separated doubled scheme"]
theorem fold_not_quasiSeparated (hU : ¬ QuasiCompact U.ι) :
    ¬ QuasiSeparated (fold U) := sorry

end AlgebraicGeometry.Scheme.DoubleAlong
