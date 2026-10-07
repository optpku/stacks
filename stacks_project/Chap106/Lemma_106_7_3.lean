module

public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap98.Lemma_98_18_2
public import stacks_project.Chap106.Lemma_106_7_3_Comparison
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation
public import stacks_project.Chap107.Situation_107_2_1_Instances

/-!
# Base change of infinitesimal deformation modules

For an algebraic stack whose structure morphism is locally of finite
presentation, infinitesimal lifts commute with flat extension of scalars of
the structure ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Lemma 106.7.3. Let `X` be an algebraic stack over a scheme `S` whose
structure morphism `X ⟶ S` is locally of finite presentation. Let `A ⟶ B`
be a flat `S`-algebra homomorphism. Let `x` be an object of `X` over `A`
and set `y = x|_B`. Then the canonical comparison
`T_x(M) ⊗[A] B ⟶ T_y(M ⊗[A] B)` is an isomorphism. -/
@[stacks 0DNT]
theorem tangentExtendScalars_isIso {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFinitePresentation
      (baseProjection.{u + 1, u, u + 1} X)]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB) (hflat : v.hom.Flat)
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    IsIso (tangentExtendScalars v hv x M) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
