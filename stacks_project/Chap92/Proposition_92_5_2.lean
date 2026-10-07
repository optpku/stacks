module

public import stacks_project.Chap92.Lemma_92_5_1_Augmentation
public import stacks_project.Chap92.Lemma_92_4_1_PolynomialOver
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.RingTheory.FiniteType
import Mathlib.Tactic.CrossRefAttribute

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

namespace Algebra

/-- A polynomial `A`-algebra is of finite type if and only if it is isomorphic as an
`A`-algebra to `MvPolynomial (Fin n) A` for some `n`. -/
theorem IsPolynomial.finiteType_iff {A P : Type u} [CommRing A] [CommRing P] [Algebra A P] :
    (IsPolynomial A P ∧ FiniteType A P) ↔
      ∃ n : ℕ, Nonempty (P ≃ₐ[A] MvPolynomial (Fin n) A) :=
  sorry

end Algebra

namespace CommRingCat.Under

/-- Proposition 92.5.2. Let `A` be a Noetherian ring. Let `A ⟶ B` be a finite type ring map.
There exists a simplicial `A`-algebra `P` with an augmentation `ε : P ⟶ B` such that each
`(P.obj n).left` is a polynomial algebra of finite type over `A` and such that
`overAugmentation P` is a trivial Kan fibration of simplicial sets. -/
@[stacks 08PX]
theorem exists_finiteType_polynomial_augmentation
    (A : CommRingCat.{u}) [IsNoetherianRing A] (B : Under A) [Algebra.FiniteType A B] :
    ∃ P : SimplicialObject (Over B),
      (∀ n, Algebra.IsPolynomial A (P.obj n).left ∧ Algebra.FiniteType A (P.obj n).left) ∧
        I.rlp (overAugmentation P) :=
  sorry

end CommRingCat.Under
