/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Countable
public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeOver

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The skeleton of finite-type schemes over a countable Noetherian affine base is countable. -/
instance countableCategory_finiteTypeOver
    (R : Type u) [CommRing R] [Countable R] [IsNoetherianRing R] :
    CountableCategory (Skeleton (Scheme.FiniteTypeOver (Spec (CommRingCat.of R)))) := sorry

end AlgebraicGeometry.Scheme
