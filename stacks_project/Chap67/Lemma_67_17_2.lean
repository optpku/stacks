/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_17_2_SchemeTheoreticDensity

/-!
# Étale-local characterization of scheme-theoretic density

Lemma 67.17.2 records that for an open immersion of algebraic spaces, the
scheme-theoretic closure of every étale preimage equalling the source is
equivalent to the same condition for some surjective étale scheme atlas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace SchemeTheoreticDensity

variable {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι]

/-- Lemma 67.17.2: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `ι : U ⟶ X` be an open immersion of algebraic spaces over `S`. The following
are equivalent: for every étale morphism `φ : V ⟶ X` of algebraic spaces, the
scheme-theoretic closure of `openInverseImage φ ι` in `V` equals `V`; and there
exists a scheme `V` over `S` and a surjective étale morphism `φ : ofOver V ⟶ X`
such that the scheme-theoretic closure of `openInverseImage φ ι` in `ofOver V`
equals `ofOver V`. -/
@[stacks 0833]
theorem tfae : List.TFAE [forallEtale ι, existsSurjectiveEtale ι] := sorry

/-- The étale-local and surjective-étale-scheme-atlas tests for scheme-theoretic
density of an open immersion are equivalent. -/
theorem forallEtale_iff_existsSurjectiveEtale :
    forallEtale ι ↔ existsSurjectiveEtale ι := sorry

end SchemeTheoreticDensity

end AlgebraicGeometry.AlgebraicSpace
