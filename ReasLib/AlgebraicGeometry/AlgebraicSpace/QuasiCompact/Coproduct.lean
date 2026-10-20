/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Countable.Small
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Finite coproducts of quasi-compact algebraic spaces

A finite disjoint union of quasi-compact algebraic spaces is again quasi-compact.
-/

@[expose] public section

open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite coproduct of quasi-compact algebraic spaces is quasi-compact. -/
instance instIsQuasiCompact_coproduct {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → AlgebraicSpace S) [∀ i, IsQuasiCompact (X i)] :
    IsQuasiCompact (coproduct X) := sorry

end AlgebraicGeometry.AlgebraicSpace
