/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointwise flatness along a relative effective Cartier divisor

This file owns the local flatness criterion at points on a relative effective Cartier divisor.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open Scheme.Hom

variable {X S : Scheme.{u}}

/-- A morphism is flat at a point of a relative effective Cartier divisor when the source local
ring is Noetherian. -/
@[stacks 062U]
theorem IsRelativeEffectiveCartierDivisor.flatAt_of_mem_support
    (f : X ⟶ S) (D : X.IdealSheafData) (x : X)
    [IsRelativeEffectiveCartierDivisor f D] [IsNoetherianRing (X.presheaf.stalk x)]
    (hx : x ∈ D.support) :
    Scheme.Hom.flatAt f x := sorry

end AlgebraicGeometry
