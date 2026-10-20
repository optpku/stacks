/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Affine
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/-- The cohomology of a quasi-coherent module is preserved by pushforward along an affine
morphism of schemes. -/
@[stacks 089W]
theorem globalCohomology_iso_pushforward_of_isAffineHom
    (f : X ⟶ S) [IsAffineHom f]
    [HasInjectiveResolutions X.Modules]
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u})]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (i : ℕ) :
    IsIsomorphic
      (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' i (⊤ : Opens X))
      (((SheafOfModules.toSheaf S.ringCatSheaf).obj
        ((Scheme.Modules.pushforward f).obj ℱ)).H' i (⊤ : Opens S)) := sorry

end AlgebraicGeometry.Scheme
