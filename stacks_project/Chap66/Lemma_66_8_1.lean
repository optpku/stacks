/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Lemma_66_8_1_Constructible

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.8.1: let `S` be a scheme, let `X` be an algebraic space over `S`, and let `E` be a
subset of `|X|`. The following are equivalent: for every étale morphism `U ⟶ X` from a scheme,
the inverse image of `E` in `U` is locally constructible; for every étale morphism `U ⟶ X` from
an affine scheme, the inverse image of `E` in `U` is constructible; for some surjective étale
morphism `U ⟶ X` from a scheme, the inverse image of `E` in `U` is locally constructible. -/
@[stacks 0ECT]
theorem isEtaleLocallyConstructible_tfae {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : Set (Points X)) :
    List.TFAE [IsEtaleLocallyConstructible E, IsEtaleLocallyConstructible.forallAffine E,
      IsEtaleLocallyConstructible.existsSurjective E] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
