/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Flat

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.22.10: fibre dimension is unchanged along a specialization `x' ⤳ x`
when `x` is generic in an irreducible component of its fibre. -/
@[stacks 054U] #check
  (AlgebraicGeometry.Scheme.Hom.fiberDimensionAt_eq_of_specializes_of_isGenericPoint_fiber :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
      {x' x : X},
      Specializes x' x →
      f.asFiber x ∈ genericPoints (f.fiber (f x)) →
      f.fiberDimensionAt x' = f.fiberDimensionAt x)

end AlgebraicGeometry.Scheme.Hom
