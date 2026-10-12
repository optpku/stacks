/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If `f : X ⟶ Y` is an integral, universally injective, and surjective morphism
of algebraic spaces, base change along `f` induces an equivalence from the
spaces-étale site of `Y` to the spaces-étale site of `X`. -/
instance spacesEtalePullback.isEquivalence
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] [UniversallyInjective f] [Surjective f] :
    (spacesEtalePullback f).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace
