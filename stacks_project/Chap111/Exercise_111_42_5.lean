/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffinePushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Exercise 111.42.5: Let `f : X ⟶ Y` be an affine morphism of schemes. Then the cohomology of a
quasi-coherent `𝒪_X`-module `ℱ` on `X` is isomorphic in every degree to the cohomology of its
pushforward on `Y`. -/
@[stacks 0D8U] #check
  (AlgebraicGeometry.Scheme.globalCohomology_iso_pushforward_of_isAffineHom :
    ∀ {X S : Scheme.{u}}
      (f : X ⟶ S) [IsAffineHom f]
      [HasInjectiveResolutions X.Modules]
      [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
      [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u})]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (i : ℕ),
      IsIsomorphic
        (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' i (⊤ : Opens X))
        (((SheafOfModules.toSheaf S.ringCatSheaf).obj
          ((Scheme.Modules.pushforward f).obj ℱ)).H' i (⊤ : Opens S)))

end AlgebraicGeometry.Scheme
