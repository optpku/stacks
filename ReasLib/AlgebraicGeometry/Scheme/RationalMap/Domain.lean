/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.RationalMap

variable {X Y : Scheme}

/-- A morphism on the domain of a rational map that represents it is the morphism of its
canonical partial-map representative. -/
theorem eq_toPartialMap_hom_of_toRationalMap [IsReduced X] [Y.IsSeparated] (φ : X ⤏ Y)
    (f : X.restrict φ.domain.isOpenEmbedding ⟶ Y)
    (hf : (⟨φ.domain, φ.dense_domain, f⟩ : X.PartialMap Y).toRationalMap = φ) :
    f = φ.toPartialMap.hom := sorry

end AlgebraicGeometry.Scheme.RationalMap
