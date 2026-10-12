/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import stacks_project.Chap79.«79_12_14_1_WithSection»
import StacksCheckRecall

/- 79.12.14.1: For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
and a section `σ : Y ⟶ X` of `f`, and for an algebraic space or a scheme `T`
over `S`, a variant pair `(a, Z)` consists of a morphism `a : T ⟶ Y` over `S`
together with an open subspace `Z : OpenSubspace (pullback a f)` of `T ×_Y X`
such that `IsFinite (Z.ι ≫ pullback.fst a f)`, i.e. `pr₀|_Z : Z ⟶ T` is finite,
and the graph `(1_T, σ ∘ a) : T ⟶ T ×_Y X` given by
`FinitePart.sectionGraph a f σ hσ` factors through `Z`. -/
@[stacks 04RQ] #check AlgebraicGeometry.AlgebraicSpace.FinitePart.WithSection
