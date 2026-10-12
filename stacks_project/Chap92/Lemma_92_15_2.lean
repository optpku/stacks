/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.«92_15_0_1_TensorProduct»
public import ReasLib.Algebra.Category.ModuleCat.Tor.TensorAction
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of the tensor-product cone

Lemma 92.15.2 records the homology of the object `E` of (92.15.0.1): it vanishes
in cohomological degrees `i ≥ -1`, and `H^{-2}(E)` is `Tor_1^R(A, B)` as a module
over `A ⊗[R] B`.
-/

@[expose] public section

open Algebra.CotangentComplex
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ModuleCat.Tor
open scoped TensorProduct

universe u

namespace Algebra.CotangentComplex

/-- Lemma 92.15.2 (1): for a ring `R` and `R`-algebras `A`, `B`, the object `E` of
(92.15.0.1) satisfies `H^i(E) = 0` for every cohomological degree `i ≥ -1`. -/
@[stacks 09DB]
theorem tensorProductCone_homology_isZero_of_ge_negOne (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)]
    {i : ℤ} (hi : -1 ≤ i) :
    IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) i).obj
        (tensorProductCone R A B)) :=
  sorry

/-- Lemma 92.15.2 (2): for a ring `R` and `R`-algebras `A`, `B`, the object `E` of
(92.15.0.1) satisfies `H^{-2}(E) = Tor_1^R(A, B)` as modules over `A ⊗[R] B`. -/
@[stacks 09DB]
theorem tensorProductCone_homology_negTwo_isIsomorphic_tor (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) (-2)).obj
        (tensorProductCone R A B))
      (TensorAction.obj 1) :=
  sorry

end Algebra.CotangentComplex
