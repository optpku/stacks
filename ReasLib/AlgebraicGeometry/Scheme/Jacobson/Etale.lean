/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.JacobsonSpace

/-- The Jacobson-space property for schemes is local for the étale precoverage. -/
instance isLocalEtale :
    ObjectProperty.IsLocal
      (fun X : Scheme.{u} ↦ JacobsonSpace X) Scheme.etalePrecoverage := sorry

end AlgebraicGeometry.Scheme.JacobsonSpace
