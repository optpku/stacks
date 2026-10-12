/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_8_1_Constructible

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.29.1: let `S` be a scheme, let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`,
and let `E ⊂ |Y|`. If `E` is étale locally constructible in `Y`, then `Points.map f ⁻¹' E` is
étale locally constructible in `X`. -/
@[stacks 0ECW]
theorem IsEtaleLocallyConstructible.preimage {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {E : Set (Points Y)} (hE : IsEtaleLocallyConstructible E) :
    IsEtaleLocallyConstructible (Points.map f ⁻¹' E) := sorry

end AlgebraicGeometry.AlgebraicSpace
