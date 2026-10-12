/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap99.«99_9_1_1_Functor»
public import stacks_project.Chap108.Lemma_108_5_1_ClosedImmersion

/-!
# Lemma 108.7.1

The relative diagonal of the Grothendieck Hilbert functor over `B` is a closed
immersion of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.7.1 (1): the diagonal of `hilbert f` over `B` is a closed immersion. -/
@[stacks 0DM6]
theorem isClosedImmersion_diagonal (f : X ⟶ B) [FinitePresentation f]
    [Separated f] :
    Quot.IsClosedImmersionOnSchemesOver (Limits.diag (hilbert f)) :=
  sorry

/-- Lemma 108.7.1 (2): the diagonal of `hilbert f` over `B` is of finite
presentation. -/
@[stacks 0DM6]
theorem finitePresentation_diagonal (f : X ⟶ B) [FinitePresentation f]
    [Separated f] :
    Quot.IsFinitePresentationOnSchemesOver (Limits.diag (hilbert f)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
