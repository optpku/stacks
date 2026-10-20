module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.Flat

/-!
# Lower semicontinuity of fibre dimensions of flat morphisms of algebraic spaces

The target-indexed fibre dimension of a flat morphism of finite presentation of
algebraic spaces is lower semicontinuous on the space of points of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

/- Lemma 76.31.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a flat morphism of
finite presentation of algebraic spaces over `S`. Let `fiberDimension f` be the
function on `Points Y` giving the dimension of fibres of `f` introduced in
Lemma 76.31.2. Then `fiberDimension f` is lower semicontinuous. -/
@[stacks 0D4P] #check
  (AlgebraicGeometry.AlgebraicSpace.lowerSemicontinuous_fiberDimension :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.Flat f]
      [AlgebraicGeometry.AlgebraicSpace.FinitePresentation f],
      LowerSemicontinuous (AlgebraicGeometry.AlgebraicSpace.fiberDimension f))
