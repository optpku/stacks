module

public import ReasLib.RingTheory.CotangentComplex.TensorProduct
public import ReasLib.Algebra.Category.ModuleCat.Tor.TensorAction
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of the tensor-product cotangent cone

For commutative algebras over a common base, the canonical tensor-product
cotangent cone has zero homology in degrees at least `-1`, and its degree `-2`
homology is the first Tor module with its canonical tensor-product algebra action.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ModuleCat.Tor
open scoped TensorProduct

universe u

namespace Algebra.CotangentComplex

/-- The canonical tensor-product cotangent cone of commutative `R`-algebras
`A` and `B` has zero homology in every cohomological degree at least `-1`. -/
@[stacks 09DB]
theorem tensorProductCone_homology_isZero_of_ge_negOne (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    {i : ℤ} (hi : -1 ≤ i) :
    IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) i).obj
        (tensorProductCone R A B)) :=
  sorry

/-- The degree `-2` homology of the canonical tensor-product cotangent cone of
commutative `R`-algebras `A` and `B` is isomorphic to `Tor_1^R(A, B)` as a module
over `A ⊗[R] B`. -/
@[stacks 09DB]
theorem tensorProductCone_homology_negTwo_isIsomorphic_tor (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) (-2)).obj
        (tensorProductCone R A B))
      (TensorAction.obj 1) :=
  sorry

end Algebra.CotangentComplex
