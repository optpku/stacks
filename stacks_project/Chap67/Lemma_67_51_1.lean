/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite

/-!
# Representability of locally quasi-finite separated morphisms

A locally quasi-finite and separated morphism of algebraic spaces over a
scheme is representable.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.51.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is locally quasi-finite and separated, then
`f` is representable. -/
@[stacks 0418]
theorem relativelyRepresentable_of_locallyQuasiFinite_separated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [Separated f] :
    yoneda.relativelyRepresentable f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
