/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.FiniteType
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.21.8: local finite presentation implies local finite type, and finite presentation implies finite type. The global implication is checked first. -/
@[stacks 01TW] #check
  (AlgebraicGeometry.Scheme.Hom.instFiniteTypeOfFinitePresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f], Scheme.Hom.FiniteType f)

/- The local implication, supplied by the canonical Mathlib instance. -/
#check
  (AlgebraicGeometry.instLocallyOfFiniteTypeOfLocallyOfFinitePresentation :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f], LocallyOfFiniteType f)
