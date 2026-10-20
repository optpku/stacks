/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ProjectionFormula.Finite
import StacksCheckRecall

/-!
# Lemma 69.4.3

For a finite morphism of algebraic spaces, the canonical projection-formula map of the
associated morphism of ringed topoi is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 69.4.3: let `S` be a scheme. Let `π : X ⟶ Y` be a finite morphism of algebraic
spaces over `S`. Let `A` be a sheaf of rings on `X_étale`. Let `B` be a sheaf of rings on
`Y_étale`. Let `φ : B ⟶ π_* A` be a homomorphism of sheaves of rings, so that we obtain a
morphism of ringed topoi `f = toRingedToposHom π φ`. For a sheaf of `A`-modules `F` and a
sheaf of `B`-modules `G`, the canonical map
`G ⊗_B f_* F ⟶ f_*(f^* G ⊗_A F)` is an isomorphism. -/
@[stacks 0DK4] #check (AlgebraicGeometry.AlgebraicSpace.IsFinite.isIso_projectionFormula :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (π : X ⟶ Y) [IsFinite π]
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (B : Sheaf (smallEtaleTopology Y) CommRingCat.{u})
    (φ : (etaleRingedSite Y B).structureSheaf ⟶
      (ringPushforward π).obj (etaleRingedSite X A).structureSheaf)
    (F : SheafOfModules.{u} (etaleRingedSite X A).structureSheaf)
    (G : SheafOfModules.{u} (etaleRingedSite Y B).structureSheaf),
    IsIso (projectionFormula π φ G F))

end AlgebraicGeometry.AlgebraicSpace
