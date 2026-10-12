/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.AlternatingFaceMapComplex
import StacksCheckRecall

@[expose] public section

/-!
# Source-facing bridge for Lemma 14.23.1

@stack 0195

The exactness theorem is shared Dold-Kan API, using Mathlib's canonical notation `K[X]` for the
alternating face map complex denoted `s(X)` in the source.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial DoldKan

universe v u

namespace AlgebraicTopology.alternatingFaceMapComplex

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (X : SimplicialObject A)

/- Lemma 14.23.1: the alternating face map complex functor is exact. -/
#check (exactFunctor (A := A) :
  SimplicialObject A ⥤ₑ ChainComplex A ℕ)

@[stacks 0195]
#check ((exactFunctor (A := A)).property :
  CategoryTheory.exactFunctor (SimplicialObject A) (ChainComplex A ℕ)
    (AlgebraicTopology.alternatingFaceMapComplex A))

#check (preservesFiniteLimits (A := A) :
  PreservesFiniteLimits (AlgebraicTopology.alternatingFaceMapComplex A))

#check (preservesFiniteColimits (A := A) :
  PreservesFiniteColimits (AlgebraicTopology.alternatingFaceMapComplex A))
#check (K[X] : ChainComplex A ℕ)

end AlgebraicTopology.alternatingFaceMapComplex
