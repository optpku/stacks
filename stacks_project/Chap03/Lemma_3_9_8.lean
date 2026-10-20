/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Size
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SizeCounterexample

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped Cardinal AlgebraicGeometry

/- Lemma 3.9.8 -/
@[stacks 04VA] #check
  (AlgebraicGeometry.Scheme.size_le_of_mono_of_quasiCompact_or_locallyOfFinitePresentation :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f],
      (QuasiCompact f ∨ LocallyOfFinitePresentation f) → X.size ≤ Y.size)

#check
  (AlgebraicGeometry.Scheme.size_le_of_mono_quasiCompact :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f] [QuasiCompact f], X.size ≤ Y.size)

#check
  (AlgebraicGeometry.Scheme.size_le_of_mono_locallyOfFinitePresentation :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f] [LocallyOfFinitePresentation f],
      X.size ≤ Y.size)

#check
  (AlgebraicGeometry.Scheme.UltrafilterCoprod.not_size_le :
    ¬ AlgebraicGeometry.Scheme.UltrafilterCoprod.source.{u}.size ≤
      AlgebraicGeometry.Scheme.UltrafilterCoprod.target.{u}.size)

end
