/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Comparison

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/- Lemma 38.34.1: a family of locally finitely presented scheme morphisms is a
`ph` covering if and only if it is a `V` covering. -/
@[stacks 0ETR] #check
  (AlgebraicGeometry.phCovering_iff_isVCovering_of_locallyOfFinitePresentation :
    ∀ {ι : Type v} {T : Scheme.{u}} (family : ι → Scheme.{u})
      (map : ∀ i, family i ⟶ T) (_ : ∀ i, LocallyOfFinitePresentation (map i)),
      PhCovering family map ↔ IsVCovering T family map)

end AlgebraicGeometry
