/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale.Locality
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 88.20.2: A morphism of locally Noetherian formal algebraic spaces is
rig-étale if and only if every affine étale chart square has a rig-étale top
arrow, if and only if an affine étale target covering admits affine étale
coverings of its fibre products with rig-étale projections, if and only if an
affine étale source covering admits rig-étale factorizations through affine
étale target charts. -/
@[stacks 0GCZ] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigEtale.tfae :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y),
    List.TFAE [RigEtale f, RigEtale.etaleAffineLocally f,
      RigEtale.existsCoverOnTarget f, RigEtale.existsCoverOnSource f])
