/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap93.Lemma_93_8_3

/-!
# Vanishing of `T Def_P` for a smooth `k`-algebra

In Example 93.8.1, if `P` is a smooth `k`-algebra, then the tangent space of
the residue-fibre slice `Def_P` consists of the single isomorphism class of
the trivial dual-number deformation `P[ε]`.
-/

@[expose] public section

open CategoryTheory Functor
open ArtinianLocalAlgCat
open RingHom.SquareZeroExtension

noncomputable section

universe u

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The zero tangent vector of `Def_P`, as the isomorphism class of the trivial
dual-number deformation `P[ε]`. -/
def trivialTangent (P : Type u) [CommRing P] [Algebra k P] :
    Functor.tangentSpace (deformationForget Λ k P) :=
  tangentSpace.mk (deformationForget Λ k P) (trivialDeformationFiber Λ k P)

/-- `trivialTangent` is the class of `trivialDeformationFiber`. -/
theorem trivialTangent_eq (P : Type u) [CommRing P] [Algebra k P] :
    trivialTangent Λ k P =
      tangentSpace.mk (deformationForget Λ k P) (trivialDeformationFiber Λ k P) :=
  sorry

/-- Lemma 93.8.4
In Example 93.8.1 let `P` be a smooth `k`-algebra. Then `T Def_P = (0)`. -/
@[stacks 0DZL]
theorem eq_trivialTangent (P : Type u) [CommRing P] [Algebra k P] [Algebra.Smooth k P]
    (x : Functor.tangentSpace (deformationForget Λ k P)) :
    x = trivialTangent Λ k P :=
  sorry

/-- If `P` is a smooth `k`-algebra, then `Ext¹_P(NL_{P/k}, P) = 0`. -/
theorem extOneNaiveCotangent_eq_zero (P : Type u) [CommRing P] [Algebra k P]
    [Algebra.Smooth k P] (ξ : extOneNaiveCotangent k P P) : ξ = 0 :=
  sorry

end FlatAlgebraCat
