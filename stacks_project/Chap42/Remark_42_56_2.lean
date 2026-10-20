/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.K0.Adams
import StacksCheckRecall

open scoped AlgebraicGeometry

universe u

/- Remark 42.56.2: if `2 : Γ(X, ⊤)` is invertible, canonical factor exchange on every
perfect derived tensor square has positive and negative perfect eigensummands, and their class
difference defines an additive second Adams operation on `K0 X`. -/
@[stacks 0FEK] #check
  (AlgebraicGeometry.Scheme.K0.exists_adamsTwo :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [Invertible (2 : Γ(X, ⊤))],
      ∃ psi : AlgebraicGeometry.Scheme.K0 X →+ AlgebraicGeometry.Scheme.K0 X,
        ∀ L : @AlgebraicGeometry.RingedSpace.ModuleDerived.Perfect X.toRingedSpace,
          ∃ positive negative :
              @AlgebraicGeometry.RingedSpace.ModuleDerived.Perfect X.toRingedSpace,
            AlgebraicGeometry.Scheme.K0.IsTensorSquareEigensplitting
                X L positive negative ∧
              psi (CategoryTheory.TriangulatedK0.of L) =
                CategoryTheory.TriangulatedK0.of positive -
                  CategoryTheory.TriangulatedK0.of negative)
