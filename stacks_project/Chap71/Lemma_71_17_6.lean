/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Definition_71_17_1_Blowup

/-!
# Lemma 71.17.6

The blowup of an algebraic space along an effective Cartier divisor is the
identity morphism of that algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- Lemma 71.17.6: let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `Z ⊂ X` be an effective Cartier divisor. The blowup of `X` in `Z` is the
identity morphism of `X`. -/
@[stacks 085V, instance]
instance instIsIso_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsEffectiveCartierDivisor Z.ι] (π : along Z) :
    IsIso π.hom :=
  sorry

/-- A chosen blowup of `X` along an effective Cartier divisor `Z` is isomorphic
over `X` to the identity morphism of `X`. -/
theorem isoOver_id {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsEffectiveCartierDivisor Z.ι] (π : along Z) :
    Nonempty (Over.mk π.hom ≅ Over.mk (𝟙 X)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
