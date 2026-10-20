/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ProjectionFormula

/-!
# Projection formula for finite morphisms

For a finite morphism of algebraic spaces, the canonical projection-formula map of the
associated morphism of ringed topoi is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a finite morphism `π : X ⟶ Y` of algebraic spaces over a scheme, étale ring
sheaves `A` on `X` and `B` on `Y`, and a homomorphism `φ : B ⟶ π_* A`, the canonical map
`G ⊗_B f_* F ⟶ f_*(f^* G ⊗_A F)` is an isomorphism for every `A`-module sheaf `F`
and `B`-module sheaf `G`, where `f = toRingedToposHom π φ`. -/
instance IsFinite.isIso_projectionFormula
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (π : X ⟶ Y) [IsFinite π]
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (B : Sheaf (smallEtaleTopology Y) CommRingCat.{u})
    (φ : (etaleRingedSite Y B).structureSheaf ⟶
      (ringPushforward π).obj (etaleRingedSite X A).structureSheaf)
    (F : SheafOfModules.{u} (etaleRingedSite X A).structureSheaf)
    (G : SheafOfModules.{u} (etaleRingedSite Y B).structureSheaf) :
    IsIso (projectionFormula π φ G F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
