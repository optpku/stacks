/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology

/-!
# Type-valued weak sheafification on the associated étale site

The inclusion of Type-valued étale sheaves into presheaves on a category
fibred in groupoids admits a left adjoint in the original coefficient universe.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The inclusion of Type-`u` sheaves on the associated étale site of a category
fibred in groupoids over a scheme into presheaves admits a left adjoint. -/
instance etaleTopology_hasWeakSheafify_type {S : Scheme.{u}} (X : GroupoidsOver S) :
    HasWeakSheafify X.etaleTopology (Type u) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
