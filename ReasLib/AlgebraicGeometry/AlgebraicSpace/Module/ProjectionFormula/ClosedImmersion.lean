/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ProjectionFormula

/-!
# Projection formula for closed immersions

For a closed immersion of algebraic spaces, the canonical projection-formula morphism
for sheaves of modules over étale ringed sites is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The projection-formula morphism for a closed immersion is an isomorphism. -/
instance IsClosedImmersion.isIso_projectionFormula
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (B : Sheaf (smallEtaleTopology Z) CommRingCat.{u})
    (φ : (etaleRingedSite X A).structureSheaf ⟶
      (ringPushforward i).obj (etaleRingedSite Z B).structureSheaf)
    (F : SheafOfModules.{u} (etaleRingedSite X A).structureSheaf)
    (G : SheafOfModules.{u} (etaleRingedSite Z B).structureSheaf) :
    IsIso (projectionFormula i φ F G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
