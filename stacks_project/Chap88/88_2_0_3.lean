/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.AdicSystem
import StacksCheckRecall

/-!
# The functor from complete algebras to adic inverse systems

The functor sends an `I`-adically complete `A`-algebra with finite-type special
fiber to its system of quotients by the extended positive powers of `I`.
-/

@[expose] public section

open CategoryTheory

universe u

/- 88.2.0.3: the functor `𝒞' ⟶ 𝒞` sending `B` to `(B ⧸ I ^ n B)_{n ≥ 1}`. -/
@[stacks 0AJN] #check (CommAlgCat.TopologicallyFiniteType.toAdicSystem :
  ∀ {A : Type u} [CommRing A], (I : Ideal A) →
    CommAlgCat.TopologicallyFiniteType.{u} A I ⥤ AdicAlgebraSystem A I)
