/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper
import StacksCheckRecall

open CategoryTheory

universe u

/- 32.14.3.1: in the commutative square `X' ⟶ Pⁿ_S`, `X' ⟶ X`, `Pⁿ_S ⟶ S`,
`X ⟶ S`, properness descends to the separated, locally finite type bottom morphism when the
left morphism is surjective and the top and right morphisms are proper. -/
@[stacks 05LZ] #check
  (AlgebraicGeometry.IsProper.of_surjective_commSq :
    ∀ {S X P X' : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {p : P ⟶ S},
      (toP : X' ⟶ P) → (π : X' ⟶ X) → CategoryTheory.CommSq toP π p f →
        [AlgebraicGeometry.Surjective π] → [AlgebraicGeometry.IsProper toP] →
          [AlgebraicGeometry.IsProper p] → [AlgebraicGeometry.IsSeparated f] →
            [AlgebraicGeometry.LocallyOfFiniteType f] → AlgebraicGeometry.IsProper f)
