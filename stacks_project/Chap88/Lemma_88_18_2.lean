/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSmooth.Locality
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 88.18.2
Rig-smoothness is equivalent to the universal affine étale chart test and to
the affine étale covering conditions on the target and source.
-/
@[stacks 0GCQ] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigSmooth.tfae :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y),
    List.TFAE [RigSmooth f, RigSmooth.etaleAffineLocally f,
      RigSmooth.existsCoverOnTarget f, RigSmooth.existsCoverOnSource f])
