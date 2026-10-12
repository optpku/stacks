/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap96.Lemma_96_19_10_Covering
public import stacks_project.Chap101.Lemma_101_25_5_Surjective
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Fppf covering lifts for morphisms of algebraic stacks

A morphism of algebraic stacks which is surjective, flat, and locally of finite
presentation has the fppf lifting property for objects of the target over a
scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.27.13: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
surjective, flat, and locally of finite presentation. Then for every scheme `U`
and object `y` of `Y` over `U` there exists an fppf covering `{U_i ⟶ U}` and
objects `x_i` of `X` over `U_i` such that `f(x_i) ≅ y|_{U_i}` in `Y_{U_i}`. -/
@[stacks 06QA]
theorem exists_fppfCovering_iso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) :
    Groupoids.Hom.existsCoveringLift StandardTopology.fppf f y :=
  sorry

end AlgebraicGeometry.AlgebraicStack
