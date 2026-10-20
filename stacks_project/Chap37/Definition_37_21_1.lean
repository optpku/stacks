/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Regular
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

/- Definition 37.21.1 (1): a scheme morphism is regular at `x` exactly when it is
flat at `x` and its residue-field fibre is geometrically regular at the distinguished
point `f.asFiber x`. -/
@[stacks 07R7] #check
  (AlgebraicGeometry.Scheme.Hom.regularAt_iff :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X),
      f.RegularAt x ↔ f.flatAt x ∧
        AlgebraicGeometry.Scheme.Hom.IsGeometricallyRegularAt
          (f.fiberToSpecResidueField (f x)) (f.asFiber x))

/- Definition 37.21.1 (2): for a morphism with locally Noetherian fibres,
regularity is equivalent to regularity at every source point. -/
@[stacks 07R7] #check
  (AlgebraicGeometry.regular_iff_forall_regularAt :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [∀ y : Y, IsLocallyNoetherian (f.fiber y)],
      AlgebraicGeometry.Regular f ↔ ∀ x : X, f.RegularAt x)
