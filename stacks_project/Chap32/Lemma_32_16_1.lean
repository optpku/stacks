/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.DVR.DenseRange
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/-
Lemma 32.16.1: let `f : X ⟶ S` and `h : U ⟶ X` be finite-type morphisms of schemes. If `S` is
locally Noetherian, `f` is separated, `h` has dense range, and every DVR-valuative square over
`f` whose generic arrow factors through `h` admits a lift, then `f` is proper.
-/
@[stacks 0CM3] #check
  (AlgebraicGeometry.ValuativeCriterion.DVR.Along.isProper_of_isSeparated :
    ∀ {U X S : Scheme.{u}} (f : X ⟶ S) (h : U ⟶ X)
      [IsLocallyNoetherian S] [Scheme.Hom.FiniteType f] [Scheme.Hom.FiniteType h]
      [IsSeparated f],
      DenseRange h → ValuativeCriterion.DVR.Along.Existence h f → IsProper f)
