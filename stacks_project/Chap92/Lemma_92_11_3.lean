module

public import stacks_project.Chap92.«92_11_1_2_Comparison»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison of the truncated cotangent complex with the naive cotangent complex

Lemma 92.11.3 records that the canonical morphism `toTruncGE_self` of 92.11.1.2,
attached to the self-presentation `A[B] ⟶ B`, is an isomorphism in `D(B)`.
-/

@[expose] public section

open CategoryTheory
open Algebra.NaiveCotangent
open CommRingCat.Under.CotangentComplex
open DerivedCategory.TStructure

universe u

noncomputable section

namespace Algebra.NaiveCotangent

/-- Lemma 92.11.3. Let `A → B` be a ring map. Then `τ_{≥ -1} L_{B/A}` is canonically
quasi-isomorphic to the naive cotangent complex. The canonical morphism is
`toTruncGE_self`, the 92.11.1.2 comparison `c : NL_{B/A} ⟶ τ_{≥ -1} L_{B/A}` attached
to the self-presentation `A[B] ⟶ B`, whose domain is the two-term complex
`I/I² ⟶ Ω_{P/A} ⊗_P B`. The same morphism is `RingHom.toTruncGE (algebraMap A B)` on
the algebra-level surface. -/
@[stacks 08RB]
instance toTruncGE_self_isIso (A : CommRingCat.{u}) (B : Under A) :
    IsIso (toTruncGE_self A B) := sorry

end Algebra.NaiveCotangent
