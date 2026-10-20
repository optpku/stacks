/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Polynomial
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra

universe u

/- Lemma 92.4.7. If `B` is a polynomial algebra over `A`, then the cotangent complex
is quasi-isomorphic to the module of relative Kähler differentials in degree zero. -/
@[stacks 08QH] #check (Algebra.CotangentComplex.isIsomorphic_single_kaehler :
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsPolynomial A B],
    CategoryTheory.IsIsomorphic
      (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj
        (ModuleCat.of B Ω[B⁄A])))
