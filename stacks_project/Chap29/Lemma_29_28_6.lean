/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.FinitePresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 29.28.6: for a locally finitely presented morphism `f : X ⟶ S`, the locus where
the local fibre dimension is at most `n` is retrocompact in `X`. -/
@[stacks 02G0] #check
  (AlgebraicGeometry.Scheme.Hom.isRetrocompact_fiberDimensionLELocus :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (n : ℕ),
      IsRetrocompact (f.fiberDimensionLELocus n))
