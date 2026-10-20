/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap99.Lemma_99_5_2
public import stacks_project.Chap99.Lemma_99_5_3
public import stacks_project.Chap108.Lemma_108_4_8_Algebraic

/-!
# Theorem 99.6.1

If `f : X ⟶ B` is a finitely presented separated morphism of algebraic spaces
over a scheme `S`, then `CohStack f` is an algebraic stack over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Theorem 99.6.1 (Algebraicity of the stack of coherent sheaves; general case):
let `S` be a scheme and let `f : X ⟶ B` be a morphism of algebraic spaces over
`S`. If `f` is of finite presentation and separated, then `Coh_{X/B}` is an
algebraic stack over `S` in the sense of Definition 94.12.1 at Hom-universe
`u + 1`. -/
@[stacks 09DS]
instance instAlgebraicStack (f : X ⟶ B) [FinitePresentation f] [Separated f] :
    AlgebraicStack (toGroupoids f) :=
  sorry

/-- `AlgebraicStack (toGroupoids f)` is equivalent to the three clauses of
Definition 94.12.1: `p f` is a stack in groupoids over `(Sch/S)_fppf`, the
diagonal of `toGroupoids f` is representable by algebraic spaces, and there is a
scheme `U` over `S` with a surjective smooth 1-morphism
`Classifying.slice U ⟶ toGroupoids f`. -/
theorem algebraicStack_iff (f : X ⟶ B) [FinitePresentation f] [Separated f] :
    AlgebraicStack (toGroupoids f) ↔
      IsStack.InGroupoids (Scheme.fppfTopology.over S) (p f) ∧
        Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal (toGroupoids f)) ∧
        ∃ (U : Over S) (π : Classifying.slice U ⟶ toGroupoids f),
          Classifying.Smooth π ∧ Classifying.Surjective π :=
  sorry

/-- An algebraic stack `toGroupoids f` admits a scheme `U` over `S` and a
surjective smooth 1-morphism `Classifying.slice U ⟶ toGroupoids f`. -/
theorem existsSmoothSurjectiveAtlas (f : X ⟶ B) [FinitePresentation f]
    [Separated f] [AlgebraicStack (toGroupoids f)] :
    ∃ (U : Over S) (π : Classifying.slice U ⟶ toGroupoids f),
      Classifying.Smooth π ∧ Classifying.Surjective π :=
  sorry

/-- If `toGroupoids f` is an algebraic stack, then fibrewise isomorphism
presheaves of `p f` are algebraic spaces, which is the 94.10.11(1) form of a
representable diagonal. -/
theorem isAlgebraicSpace_of_algebraicStack (f : X ⟶ B) [FinitePresentation f]
    [Separated f] [AlgebraicStack (toGroupoids f)] :
    isAlgebraicSpace f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
