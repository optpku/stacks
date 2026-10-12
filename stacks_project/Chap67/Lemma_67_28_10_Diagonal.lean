/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation

/-!
# Diagonals of finite presentation morphisms of algebraic spaces

The relative diagonal of a locally of finite type morphism of algebraic spaces
is locally of finite presentation. Under quasi-separatedness, the diagonal is
of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyOfFinitePresentation

/-- The relative diagonal of a locally of finite type morphism of algebraic
spaces is locally of finite presentation. -/
instance diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation (pullback.diagonal f) := sorry

end LocallyOfFinitePresentation

namespace FinitePresentation

/-- The relative diagonal of a quasi-separated locally of finite type morphism
of algebraic spaces is of finite presentation. -/
instance diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [LocallyOfFiniteType f] :
    FinitePresentation (pullback.diagonal f) := sorry

end FinitePresentation

end AlgebraicGeometry.AlgebraicSpace
