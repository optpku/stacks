/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Frobenius

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

universe u

/- Theorem 64.3.9. Arithmetic Frobenius acts on geometric étale cohomology
as the inverse of geometric Frobenius pullback. -/
@[stacks 03SV] #check
  (AlgebraicGeometry.SchemeOverField.arithmeticFrobenius_etaleHq_eq_inv_geometricFrobenius :
    ∀ {k : Type u} [Field k] [Fintype k]
      {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
      [∀ Z : Scheme.{u},
        HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
      (X : SchemeOverField k)
      (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ),
      galoisEtaleHq X F j (FiniteField.arithmeticFrobenius k) =
        CategoryTheory.inv (geometricFrobeniusEtaleHq X F j))
