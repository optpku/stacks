/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Operations
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.Topology.KrullDimension.Local

/-!
# Dimension of products over a field

Local and global Krull dimensions are additive for products of locally algebraic schemes over a
field.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The local Krull dimension of a product of locally algebraic schemes over a field is the sum of
the local dimensions at the two projected points. -/
theorem topologicalKrullDimAt_pullback_eq_add
    (X Y : SchemeOverField k) [LocallyAlgebraic X] [LocallyAlgebraic Y]
    (z : (pullback X.hom Y.hom : Scheme)) :
    topologicalKrullDimAt z =
      topologicalKrullDimAt (pullback.fst X.hom Y.hom z) +
        topologicalKrullDimAt (pullback.snd X.hom Y.hom z) := sorry

/-- The Krull dimension of a product of locally algebraic schemes over a field is the sum of their
Krull dimensions. -/
theorem topologicalKrullDim_pullback_eq_add
    (X Y : SchemeOverField k) [LocallyAlgebraic X] [LocallyAlgebraic Y] :
    topologicalKrullDim (pullback X.hom Y.hom : Scheme) =
      topologicalKrullDim X.left + topologicalKrullDim Y.left := sorry

end AlgebraicGeometry.SchemeOverField
