/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigFlat.Locality
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 88.16.2: Rig-flatness of a morphism of locally Noetherian formal algebraic
spaces is equivalent to the universal affine étale chart condition and to the
affine étale covering conditions on the target and the source. -/
@[stacks 0GGY] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigFlat.tfae :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y),
    List.TFAE [RigFlat f, RigFlat.etaleAffineLocally f,
      RigFlat.existsCoverOnTarget f, RigFlat.existsCoverOnSource f])
