module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.LimitPreservingOnObjects
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor.Fiber
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.YonedaSlice
open AlgebraicSpace
open scoped Bicategory Cardinal

universe u

/- Lemma 97.5.5: Let `S` be a scheme. Let `κ = T.left.size` for some
`T : Over S`. Let `f : X ⟶ Y` be a 1-morphism of categories fibred in groupoids
over `(Sch/S)_fppf` such that `Y ⟶ (Sch/S)_fppf` is limit preserving on objects,
for an affine scheme `V` locally of finite presentation over `S` and
`y ∈ Ob(Y_V)` the fibre product `(Sch/V)_fppf ×_{y, Y} X` is representable by an
algebraic space of size `≤ κ`, and `X` and `Y` are stacks for the Zariski
topology. Then `f` is representable by algebraic spaces. -/
@[stacks 07WH] #check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.of_limitPreservingOnObjects :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (T : Over S)
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} Y)]
    [IsStack.InGroupoids (Scheme.zariskiTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.zariskiTopology.over S) Y.p]
    (h : ∀ (V : Over S) [IsAffine V.left] [LocallyOfFinitePresentation V.hom]
      (y : Y.p.Fiber V),
      ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver V),
        RepresentsBaseChange f (YonedaSlice.representative y) Fy fy ∧
          sizeLE T.left.size Fy),
    relativelyRepresentableByAlgebraicSpaces f)

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.of_limitPreservingOnObjects_slice :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (T : Over S)
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} Y)]
    [IsStack.InGroupoids (Scheme.zariskiTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.zariskiTopology.over S) Y.p]
    (h : ∀ (V : Over S) [IsAffine V.left] [LocallyOfFinitePresentation V.hom]
      (y : GroupoidsOver.slice V ⟶ Y),
      ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver V),
        RepresentsBaseChange f y Fy fy ∧ sizeLE T.left.size Fy),
    relativelyRepresentableByAlgebraicSpaces f)
