module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.ProperFlat

/-!
# Local constancy of fibre dimensions of proper flat morphisms of algebraic spaces

The target-indexed fibre dimension of a proper, flat, finitely presented morphism of
algebraic spaces is locally constant on the space of points of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.31.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a proper, flat,
finitely presented morphism of algebraic spaces over `S`. Let `fiberDimension f`
be the function on `Points Y` giving the dimension of fibres of `f` introduced
in Lemma 76.31.2. Then `fiberDimension f` is locally constant. -/
@[stacks 0D4R] #check
  (AlgebraicGeometry.AlgebraicSpace.isLocallyConstant_fiberDimension :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [Flat f] [FinitePresentation f],
      IsLocallyConstant (fiberDimension f))

end AlgebraicGeometry.AlgebraicSpace
