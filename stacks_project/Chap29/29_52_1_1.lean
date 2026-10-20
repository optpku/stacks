/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFormula
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- 29.52.1.1: for a dominant locally finite-type morphism of integral schemes with locally
Noetherian target, the dimension of the source stalk plus the residue-field transcendence degree
is at most the dimension of the target stalk plus the function-field transcendence degree. -/
@[stacks 02JV] #check
  (AlgebraicGeometry.Scheme.Hom.DimensionFormula.stalk_add_trdeg_le_functionFieldTrdeg :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.IsLocallyNoetherian S]
      [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral S]
      [AlgebraicGeometry.IsDominant f] (x : X),
      ringKrullDim (X.presheaf.stalk x) + f.residueFieldTrdegAt x ≤
        ringKrullDim (S.presheaf.stalk (f x)) +
          f.functionFieldTrdeg f.map_genericPoint_eq_of_isDominant)
