/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_38_1_GUnramified
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation

/-!
# G-unramified morphisms of algebraic spaces versus unramified morphisms
locally of finite presentation

A morphism of algebraic spaces is G-unramified if and only if it is unramified
and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.38.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is G-unramified if and only if `f` is
unramified and locally of finite presentation. -/
@[stacks 04G1]
theorem gUnramified_iff_unramified_and_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    GUnramified f ↔ Unramified f ∧ LocallyOfFinitePresentation f :=
  sorry

/-- A G-unramified morphism of algebraic spaces is locally of finite
presentation. -/
instance locallyOfFinitePresentation_of_gUnramified {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [GUnramified f] :
    LocallyOfFinitePresentation f :=
  sorry

/-- An unramified morphism of algebraic spaces that is locally of finite
presentation is G-unramified. -/
instance gUnramified_of_unramified_of_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Unramified f]
    [LocallyOfFinitePresentation f] : GUnramified f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
