/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.QuasiFinite
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 29.29.5

The quasi-finite/relative-dimension-zero bridges are maintained in
`ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.QuasiFinite`.
-/

open AlgebraicGeometry

universe u

/- Lemma 29.29.5: for a locally finite-type morphism, quasi-finiteness at a
point is equivalent to zero local fibre dimension; globally, local
quasi-finiteness is equivalent to relative dimension zero. -/
@[stacks 0397]
#check (AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_iff_fiberDimensionAt_eq_zero :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X),
    f.QuasiFiniteAt x ↔ f.fiberDimensionAt x = (0 : WithBot ℕ∞))

#check (AlgebraicGeometry.Scheme.Hom.locallyQuasiFinite_iff_relativeDimension_zero :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f],
    LocallyQuasiFinite f ↔ AlgebraicGeometry.Scheme.Hom.RelativeDimension f 0)
