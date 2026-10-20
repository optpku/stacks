/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Functor
public import Mathlib.CategoryTheory.Sites.Sheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.StandardTopology

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- The compatible-triple functor of a contraction situation is a sheaf for
the étale topology on locally Noetherian schemes over the base. -/
theorem isSheaf_etale (σ : ContractionSituation S) :
    Presheaf.IsSheaf (locallyNoetherianTopology StandardTopology.etale S)
      σ.functor :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
