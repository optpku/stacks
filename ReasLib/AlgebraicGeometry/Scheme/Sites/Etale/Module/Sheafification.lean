/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheafification

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Sheafification of small-étale module presheaves makes the sheaf inclusion
a right adjoint. -/
instance (priority := 1100) moduleHasWeakSheafify (S : Scheme.{u}) (Λ : Type u)
    [Ring Λ] [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)] :
    HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} Λ) :=
  HasSheafify.isRightAdjoint

end AlgebraicGeometry.Scheme.Etale
