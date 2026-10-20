module

public import ReasLib.RingTheory.CotangentComplex.TensorProduct.Homology
import StacksCheckRecall

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

/- Lemma 92.15.2 (1): for a ring `R` and `R`-algebras `A`, `B`, the object `E` of
(92.15.0.1) satisfies `H^i(E) = 0` for every cohomological degree `i ≥ -1`. -/
@[stacks 09DB] #check (Algebra.CotangentComplex.tensorProductCone_homology_isZero_of_ge_negOne :
  ∀ (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    {i : ℤ}, -1 ≤ i →
    IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) i).obj
        (tensorProductCone R A B)))

/- Lemma 92.15.2 (2): for a ring `R` and `R`-algebras `A`, `B`, the object `E` of
(92.15.0.1) satisfies `H^{-2}(E) = Tor_1^R(A, B)` as modules over `A ⊗[R] B`. -/
@[stacks 09DB] #check (Algebra.CotangentComplex.tensorProductCone_homology_negTwo_isIsomorphic_tor :
  ∀ (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B],
    IsIsomorphic
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) (-2)).obj
        (tensorProductCone R A B))
      (TensorAction.obj 1))
