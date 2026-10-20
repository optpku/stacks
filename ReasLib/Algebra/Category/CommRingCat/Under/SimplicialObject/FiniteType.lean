module

public import ReasLib.Algebra.Category.CommRingCat.Under.SimplicialObject.Augmentation
public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.RingTheory.FiniteType

/-!
# Finite type of the next term of a coskeletal simplicial algebra

A coskeletal simplicial algebra with a trivial Kan augmentation and finite-type terms
through the coskeletal degree has a finite-type term in the next degree.
-/

@[expose] public section

open CategoryTheory
open Opposite
open SimplicialObject
open SSet.modelCategoryQuillen
open scoped Simplicial

universe u

namespace CommRingCat.Under

/-- Over a Noetherian ring `A` and a finite-type `A`-algebra `B`, an `n`-coskeletal
simplicial object of `A`-algebra maps to `B` with trivial Kan augmentation and finite-type
terms in every degree `k ≤ n` has a finite-type `A`-algebra in degree `n + 1`. -/
theorem finiteType_succ_of_isCoskeletal
    {A : CommRingCat.{u}} [IsNoetherianRing A] {B : Under A} [Algebra.FiniteType A B]
    {n : ℕ} (P : SimplicialObject (Over B)) [P.IsCoskeletal n]
    (h_finiteType : ∀ k ≤ n, Algebra.FiniteType A (P.obj (op ⦋k⦌)).left)
    (h_trivialKan : I.rlp (overAugmentation P)) :
    Algebra.FiniteType A (P.obj (op ⦋n + 1⦌)).left := sorry

end CommRingCat.Under
