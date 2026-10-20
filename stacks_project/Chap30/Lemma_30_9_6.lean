/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Neighborhood
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 30.9.6: let `X` be a locally Noetherian scheme, let `G` and `F` be coherent
`𝒪_X`-modules, and let `x : X`. Every morphism `G_x ⟶ F_x` is induced by a morphism between
the restrictions of `G` and `F` to some open neighborhood of `x`. -/
@[stacks 01Y4] #check
  (AlgebraicGeometry.Scheme.Modules.IsCoherent.existsNeighborhood_restrictHom_of_stalkHom :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {G F : X.Modules} [G.IsCoherent] [F.IsCoherent]
      (x : X) (ψ : RingedSpace.stalkModuleCat G x ⟶ RingedSpace.stalkModuleCat F x),
      ∃ (U : X.Opens) (hxU : x ∈ U)
        (φ : (Scheme.Modules.restrictFunctor U.ι).obj G ⟶
          (Scheme.Modules.restrictFunctor U.ι).obj F),
        AlgebraicGeometry.Scheme.Modules.stalkAddHomOfRestrictHom x U hxU φ =
          (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map ψ)
