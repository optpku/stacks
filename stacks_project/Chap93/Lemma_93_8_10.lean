/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.AdicCompletion

/-!
# Completion of ring deformations

A Noetherian `k`-algebra `P` with ideal `J` has a natural functor from its
 deformation category to the deformation category of its `J`-adic completion.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 93.8.10
In Example 93.8.1 let `P` be a `k`-algebra. Assume `P` Noetherian and let
`J ⊂ P` be an ideal. Its `J`-adic completion has a natural functor from
deformations of `P` to deformations of `AdicCompletion J P`.
-/
@[stacks 0DYV] #check (FlatAlgebraCat.adicCompletionFunctor Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P] [IsNoetherianRing P] (J : Ideal P),
    FlatAlgebraCat.deformationCategory Λ k P ⥤
      FlatAlgebraCat.deformationCategory Λ k (AdicCompletion J P))

#check (FlatAlgebraCat.adicCompletionFunctor_obj_left :
  ∀ {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P] (J : Ideal P)
    (ξ : FlatAlgebraCat.deformationCategory Λ k P),
    ((FlatAlgebraCat.adicCompletionFunctor Λ k P J).obj ξ).left =
      FlatAlgebraCat.adicCompletionObj J ξ.hom)

#check (FlatAlgebraCat.adicCompletionFunctor_comp_forget :
  ∀ {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P] (J : Ideal P),
    FlatAlgebraCat.adicCompletionFunctor Λ k P J ⋙
        FlatAlgebraCat.deformationForget Λ k (AdicCompletion J P) =
      FlatAlgebraCat.deformationForget Λ k P)
