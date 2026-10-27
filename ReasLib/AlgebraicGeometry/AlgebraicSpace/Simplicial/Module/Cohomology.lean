/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SpacesPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.QCoh.Category

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open Functor
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Module pullback along the degree-`n` map of a simplicial augmentation. -/
def stageModulePullback (n : ℕ) :
    RingedSite.ModuleCat.{u} (spacesRingedSite X) ⥤
      RingedSite.ModuleCat.{u} (spacesRingedSite (U.obj (op ⦋n⦌))) :=
  spacesModulePullback (a.app (op ⦋n⦌))

/-- Stage module pullback evaluates to module pullback along the stage augmentation map. -/
theorem stageModulePullback_obj (n : ℕ)
    (F : RingedSite.ModuleCat.{u} (spacesRingedSite X)) :
    (stageModulePullback a n).obj F =
      (spacesModulePullback (a.app (op ⦋n⦌))).obj F := rfl

/-- Pullback to a simplicial stage preserves quasi-coherence. -/
theorem stageModulePullback_mem_spacesQuasiCoherentModuleProperty (n : ℕ)
    {F : RingedSite.ModuleCat.{u} (spacesRingedSite X)}
    (hF : spacesQuasiCoherentModuleProperty X F) :
    spacesQuasiCoherentModuleProperty (U.obj (op ⦋n⦌))
      ((stageModulePullback a n).obj F) := sorry

/-- Cohomology of the module pulled back to a simplicial stage, functorially in coefficients. -/
def stageModuleCohomologyFunctor (p q : ℕ) :
    RingedSite.ModuleCat.{u} (spacesRingedSite X) ⥤ AddCommGrpCat.{u + 1} :=
  stageModulePullback a p ⋙ spacesEtaleModuleCohomologyFunctor (U.obj (op ⦋p⦌)) q

/-- The degree-`q` cohomology group of the degree-`p` stage module pullback. -/
abbrev stageModuleCohomology (F : RingedSite.ModuleCat.{u} (spacesRingedSite X))
    (p q : ℕ) : AddCommGrpCat.{u + 1} :=
  (stageModuleCohomologyFunctor a p q).obj F

/-- Stage module cohomology is ordinary spaces-étale cohomology of the stage pullback. -/
theorem stageModuleCohomology_eq (F : RingedSite.ModuleCat.{u} (spacesRingedSite X))
    (p q : ℕ) :
    stageModuleCohomology a F p q =
      spacesEtaleModuleCohomology (U.obj (op ⦋p⦌))
        ((stageModulePullback a p).obj F) q := rfl

end AlgebraicGeometry.AlgebraicSpace.Simplicial
