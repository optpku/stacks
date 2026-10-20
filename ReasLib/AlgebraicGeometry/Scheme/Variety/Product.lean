/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# Products of varieties

This module records closure of varieties over algebraically closed fields under
scheme-theoretic fibre products.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The fibre product of two varieties over an algebraically closed field, equipped with its
structure morphism through the first projection, is a variety. -/
instance instVarietyPullbackOverSpecOfVarieties
    [IsAlgClosed k] (X Y : Over (Spec (CommRingCat.of k))) [Variety X] [Variety Y] :
    Variety (Over.mk (pullback.fst X.hom Y.hom ≫ X.hom)) := sorry

/-- The categorical product of varieties over an algebraically closed field is a variety. -/
instance instVarietyProd [IsAlgClosed k]
    (X Y : Over (Spec (CommRingCat.of k))) [Variety X] [Variety Y] : Variety (X ⨯ Y) := sorry

end AlgebraicGeometry
