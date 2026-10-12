/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap75.Definition_75_9_1_Square

/-!
# Lemma 81.9.1

The fibre-product square of an elementary distinguished square of algebraic
spaces over a scheme `S` is a pushout in `AlgebraicSpace S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare

/-- Lemma 81.9.1. Let `S` be a scheme. Let `(U ⊂ W, f : V ⟶ W)` be an elementary
distinguished square of algebraic spaces over `S`. Then the fibre-product square
`U ×_W V ⟶ V`, `U ×_W V ⟶ U`, `U ⟶ W`, `V ⟶ W` is a pushout in `AlgebraicSpace S`. -/
@[stacks 0DVI]
theorem isPushout {S : Scheme.{u}} {P U V W : AlgebraicSpace S}
    (j : U ⟶ W) (f : V ⟶ W) {pU : P ⟶ U} {pV : P ⟶ V}
    [IsElementaryDistinguishedSquare j f] (h : IsPullback pU pV j f) :
    IsPushout pU pV j f :=
  sorry

/-- The chosen fibre product `U ×_W V` of an elementary distinguished square
`(j : U ⟶ W, f : V ⟶ W)` is a pushout square in `AlgebraicSpace S`. -/
theorem isPushout_pullback {S : Scheme.{u}} {U V W : AlgebraicSpace S}
    (j : U ⟶ W) (f : V ⟶ W) [IsElementaryDistinguishedSquare j f] :
    IsPushout (pullback.fst j f) (pullback.snd j f) j f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare
