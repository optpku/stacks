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
public import stacks_project.Chap108.Lemma_108_5_1_ClosedImmersion

/-!
# Lemma 108.5.1

The relative diagonal of the Grothendieck Quot functor over `B` is a closed
immersion, and of finite presentation when the source module is of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.5.1 (1): the diagonal of `quot f F` over `B` is a closed immersion. -/
@[stacks 0DM2]
theorem isClosedImmersion_diagonal (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F : X.Modules) [F.IsQuasicoherent] :
    IsClosedImmersionOnSchemesOver (Limits.diag (quot f F)) :=
  sorry

/-- Lemma 108.5.1 (2): if `F` is of finite type, then the diagonal of `quot f F`
over `B` is of finite presentation. -/
@[stacks 0DM2]
theorem finitePresentation_diagonal (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    IsFinitePresentationOnSchemesOver (Limits.diag (quot f F)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
