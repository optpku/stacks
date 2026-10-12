/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap93.Example_93_8_1_Rings
public import stacks_project.Chap93.Lemma_93_8_10_AdicCompletion

/-!
# Completion of ring deformations

Stacks 0DYV: a Noetherian `k`-algebra `P` with ideal `J` has a natural
functor `Def_P ⟶ Def_{AdicCompletion J P}` of deformation categories.
-/

@[expose] public section

open CategoryTheory Functor

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- Lemma 93.8.10
In Example 93.8.1 let `P` be a `k`-algebra. Assume `P` Noetherian and let
`J ⊂ P` be an ideal. Denote `AdicCompletion J P` the `J`-adic completion.
There is a natural functor
`deformationCategory P ⟶ deformationCategory (AdicCompletion J P)`
of deformation categories.
-/
@[stacks 0DYV]
abbrev adicCompletionFunctor (P : Type u) [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) :=
  FlatAlgebraCat.adicCompletionFunctor Λ k P J

/-- The object map of `adicCompletionFunctor` sends a deformation `(A, Q)` of
`P` to the completed pair `(A, AdicCompletion (Ideal.comap ξ.hom.toRingHom J) Q)`
over `AdicCompletion J P`. -/
theorem adicCompletionFunctor_obj_spec (P : Type u) [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) (ξ : deformationCategory Λ k P) :
    ((adicCompletionFunctor Λ k P J).obj ξ).left =
      FlatAlgebraCat.adicCompletionObj J ξ.hom := sorry

/-- Completing a deformation does not change the underlying object of `C_Λ`. -/
theorem adicCompletionFunctor_comp_forget (P : Type u) [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) :
    adicCompletionFunctor Λ k P J ⋙
        FlatAlgebraCat.deformationForget Λ k (AdicCompletion J P) =
      FlatAlgebraCat.deformationForget Λ k P := sorry
