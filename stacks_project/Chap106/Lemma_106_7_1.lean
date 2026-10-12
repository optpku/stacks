/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap106.Lemma_106_7_1_Comparison

/-!
# Base change of infinitesimal automorphism modules

For an algebraic stack whose inertia morphism is locally of finite presentation,
infinitesimal automorphisms commute with flat extension of scalars of the
structure ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Lemma 106.7.1. Let `X` be an algebraic stack over a scheme `S`. Assume
`I_X ⟶ X` is locally of finite presentation. Let `A ⟶ B` be a flat
`S`-algebra homomorphism. Let `x` be an object of `X` over `A` and set
`y = x|_B`. Then the canonical comparison
`Inf_x(M) ⊗[A] B ⟶ Inf_y(M ⊗[A] B)` is an isomorphism. -/
@[stacks 0DNR]
theorem infExtendScalars_isIso {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [HasStrongRimSchlessinger X]
    [Groupoids.Hom.LocallyOfFinitePresentation (forget.{u + 1, u, u, u + 1} X)]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB) (hflat : v.hom.Flat)
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    IsIso (infExtendScalars v hv x M) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
