module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap97.«97_5_0_1_OnObjects»
public import stacks_project.Chap97.Lemma_97_5_5_Size

/-!
# Checking representability using limit preservation on objects

A 1-morphism of Zariski stacks in groupoids over `(Sch/S)_fppf` is representable
by algebraic spaces as soon as the target is limit preserving on objects and
affine locally finite presentation tests are represented by algebraic spaces of
bounded size.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor.Fiber
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.YonedaSlice
open AlgebraicSpace
open scoped Bicategory Cardinal

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Lemma 97.5.5: Let `S` be a scheme. Let `κ = T.left.size` for some
`T : Over S`. Let `f : X ⟶ Y` be a 1-morphism of categories fibred in groupoids
over `(Sch/S)_fppf` such that `Y ⟶ (Sch/S)_fppf` is limit preserving on objects,
for an affine scheme `V` locally of finite presentation over `S` and
`y ∈ Ob(Y_V)` the fibre product `(Sch/V)_fppf ×_{y, Y} X` is representable by an
algebraic space of size `≤ κ`, and `X` and `Y` are stacks for the Zariski
topology. Then `f` is representable by algebraic spaces. -/
@[stacks 07WH]
theorem relativelyRepresentableByAlgebraicSpaces.of_limitPreservingOnObjects
    {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (T : Over S)
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} Y)]
    [IsStack.InGroupoids (Scheme.zariskiTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.zariskiTopology.over S) Y.p]
    (h : ∀ (V : Over S) [IsAffine V.left] [LocallyOfFinitePresentation V.hom]
      (y : Y.p.Fiber V),
      ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver V),
        RepresentsBaseChange f (YonedaSlice.representative y) Fy fy ∧
          sizeLE T.left.size Fy) :
    relativelyRepresentableByAlgebraicSpaces f :=
  sorry

/-- The same criterion, stated with slice tests `y : GroupoidsOver.slice V ⟶ Y`
in the form used by `relativelyRepresentableByAlgebraicSpaces`. -/
theorem relativelyRepresentableByAlgebraicSpaces.of_limitPreservingOnObjects_slice
    {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (T : Over S)
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} Y)]
    [IsStack.InGroupoids (Scheme.zariskiTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.zariskiTopology.over S) Y.p]
    (h : ∀ (V : Over S) [IsAffine V.left] [LocallyOfFinitePresentation V.hom]
      (y : GroupoidsOver.slice V ⟶ Y),
      ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver V),
        RepresentsBaseChange f y Fy fy ∧ sizeLE T.left.size Fy) :
    relativelyRepresentableByAlgebraicSpaces f :=
  sorry

end AlgebraicGeometry
