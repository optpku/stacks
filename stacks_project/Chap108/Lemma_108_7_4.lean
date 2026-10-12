/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap108.Lemma_108_7_4_Map

/-!
# Lemma 108.7.4

An open immersion of separated finite-presentation algebraic spaces over `B`
induces an open immersion of Hilbert functors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

/-- Lemma 108.7.4: If `π : X ⟶ Y` is an open immersion of algebraic spaces which
are separated and of finite presentation over an algebraic space `B`, then `π`
induces an open immersion `map π y : hilbert (π ≫ y) ⟶ hilbert y`. -/
@[stacks 0DPE]
theorem isOpenImmersion_map {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (π : X ⟶ Y) (y : Y ⟶ B) [IsOpenImmersion π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] :
    IsOpenImmersionOnSchemesOver (map π y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
