/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import stacks_project.Chap93.Lemma_93_9_7_Algebras
public import stacks_project.Chap93.Lemma_93_9_7_GlobalSections

/-!
# Affine scheme deformations versus algebra deformations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace FlatSchemeCat

variable (Λ k P : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k] [CommRing P] [Algebra k P]

/-- Lemma 93.9.7: In Example 93.9.1 let `X = Spec(P)` be an affine scheme over `k`.
With `FlatAlgebraCat.deformationCategory P` as in Example 93.8.1, global sections
`(A, Y) ↦ Γ(Y, ⊤)` is a natural equivalence of deformation categories. -/
@[stacks 0DYX, instance]
instance instIsEquivalence_globalSectionsBasedFunctor :
    BasedFunctor.IsEquivalence (globalSectionsBasedFunctor Λ k P) :=
  sorry

end FlatSchemeCat
