module

public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap101.Lemma_101_27_14_Covering
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Fppf covering lifts for a jointly surjective family of algebraic stacks

A family of morphisms of algebraic stacks which are each flat and locally of
finite presentation and which jointly cover the target on points has the fppf
lifting property for objects of the target over a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u v

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.27.14: Let `f j : Xj j ⟶ X`, `j ∈ J` be a family of morphisms of
algebraic stacks which are each flat and locally of finite presentation and
which are jointly surjective, i.e., `|X| = ⋃ |f j|(|Xj j|)`. Then for every
scheme `U` and object `x` of `X` over `U` there exists an fppf covering
`{U_i ⟶ U}_{i ∈ I}`, a map `a : I → J`, and objects `x_i` of `Xj (a i)` over
`U_i` such that `f (a i) (x_i) ≅ x|_{U_i}` in `X_{U_i}`. -/
@[stacks 07AN]
theorem exists_fppfCoveringFamily_iso {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {J : Type v} {Xj : J → GroupoidsOver S}
    [∀ j, AlgebraicStack (Xj j)] (f : ∀ j, Xj j ⟶ X)
    [∀ j, Flat (f j)] [∀ j, LocallyOfFinitePresentation (f j)]
    (h_cover : ∀ y : Points X, ∃ j, y ∈ Set.range (Points.map (f j)))
    {U : Over S} (x : GroupoidsOver.slice U ⟶ X) :
    Groupoids.Hom.existsCoveringFamilyLift StandardTopology.fppf f x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
