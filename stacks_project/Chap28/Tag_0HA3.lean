/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GScheme
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Definition (0HA3): a scheme is a G-scheme if every point has an affine open
neighbourhood whose ring of sections is a G-ring. -/
@[stacks 0HA3] #check (AlgebraicGeometry.Scheme.GScheme : Scheme.{u} → Prop)

variable (X : Scheme.{u})

#check (AlgebraicGeometry.Scheme.gScheme_iff X :
  X.GScheme ↔ ∀ x : X, ∃ U : X.affineOpens, x ∈ U ∧ IsGRing Γ(X, U))
