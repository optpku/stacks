/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Polynomial.FiniteType
public import ReasLib.Algebra.Category.CommRingCat.Under.SimplicialObject.Augmentation
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-!
# Finite-type polynomial simplicial resolutions

Finite-type algebras over Noetherian rings admit simplicial resolutions by finite-type
polynomial algebras with trivial Kan fibrations as augmentations.
-/

@[expose] public section

open CategoryTheory
open SSet.modelCategoryQuillen

universe u

namespace CommRingCat.Under

/-- A finite-type algebra `B` over a Noetherian ring `A` admits a simplicial object of
`A`-algebra maps to `B` whose terms are finite-type polynomial `A`-algebras and whose
canonical augmentation is a trivial Kan fibration of simplicial sets. -/
theorem exists_finiteType_polynomial_augmentation
    (A : CommRingCat.{u}) [IsNoetherianRing A] (B : Under A) [Algebra.FiniteType A B] :
    ∃ P : SimplicialObject (Over B),
      (∀ n, Algebra.IsPolynomial A (P.obj n).left ∧ Algebra.FiniteType A (P.obj n).left) ∧
        I.rlp (overAugmentation P) :=
  sorry

end CommRingCat.Under
