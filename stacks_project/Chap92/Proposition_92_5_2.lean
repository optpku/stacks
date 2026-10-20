/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Polynomial.FiniteType
public import ReasLib.Algebra.Category.CommRingCat.Under.SimplicialObject.PolynomialResolution
import StacksCheckRecall

/-!
# Finite-type polynomial simplicial augmentations

If `A` is Noetherian and `A ⟶ B` is of finite type, there is a simplicial object of
`A`-algebra maps to `B` whose terms are finite-type polynomial `A`-algebras and whose
augmentation is a trivial Kan fibration of simplicial sets.
-/

@[expose] public section

open CategoryTheory
open SSet.modelCategoryQuillen

universe u

#check (Algebra.IsPolynomial.finiteType_iff :
  ∀ {A P : Type u} [CommRing A] [CommRing P] [Algebra A P],
    (Algebra.IsPolynomial A P ∧ Algebra.FiniteType A P) ↔
      ∃ n : ℕ, Nonempty (P ≃ₐ[A] MvPolynomial (Fin n) A))

/- Proposition 92.5.2. Let `A` be a Noetherian ring. Let `A ⟶ B` be a finite type ring map.
There exists a simplicial `A`-algebra `P` with an augmentation `ε : P ⟶ B` such that each
`(P.obj n).left` is a polynomial algebra of finite type over `A` and such that
`CommRingCat.Under.overAugmentation P` is a trivial Kan fibration of simplicial sets. -/
@[stacks 08PX] #check (CommRingCat.Under.exists_finiteType_polynomial_augmentation :
  ∀ (A : CommRingCat.{u}) [IsNoetherianRing A] (B : Under A) [Algebra.FiniteType A B],
    ∃ P : SimplicialObject (Over B),
      (∀ n, Algebra.IsPolynomial A (P.obj n).left ∧ Algebra.FiniteType A (P.obj n).left) ∧
        I.rlp (CommRingCat.Under.overAugmentation P))
