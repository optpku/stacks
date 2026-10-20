/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine

/-!
# Vanishing of first cohomology for quasi-coherent modules

This module defines étale cohomology for module sheaves on an algebraic space and the
property that first cohomology vanishes on every quasi-coherent module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Étale sheaf cohomology of a module sheaf on an algebraic space. -/
noncomputable abbrev cohomology {S : Scheme.{u}} (X : AlgebraicSpace S) (F : Modules X) (n : ℕ)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] : AddCommGrpCat.{u} :=
  (Sheaf.functorH (smallEtaleTopology X) n).obj
    ((SheafOfModules.toSheaf (structureSheaf X)).obj F)

/-- Cohomology of a module sheaf is `Sheaf.functorH` of its underlying abelian étale sheaf. -/
theorem cohomology_eq {S : Scheme.{u}} (X : AlgebraicSpace S) (F : Modules X) (n : ℕ)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] :
    cohomology X F n =
      (Sheaf.functorH (smallEtaleTopology X) n).obj
        ((SheafOfModules.toSheaf (structureSheaf X)).obj F) :=
  rfl

/-- An algebraic space has vanishing first cohomology when every quasi-coherent module sheaf has
vanishing first cohomology. -/
@[mk_iff]
class HasVanishingH1 {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] : Prop where
  /-- First cohomology of every quasi-coherent `𝒪_X`-module vanishes. -/
  vanishing : ∀ (F : Modules X), quasiCoherentModuleProperty X F → IsZero (cohomology X F 1)

namespace HasVanishingH1

/-- A pointwise vanishing hypothesis on quasi-coherent modules yields `HasVanishingH1`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    (h : ∀ (F : Modules X), quasiCoherentModuleProperty X F → IsZero (cohomology X F 1)) :
    HasVanishingH1 X :=
  sorry

end HasVanishingH1

/-- Vanishing of first cohomology is equivalent to vanishing on the full category of
quasi-coherent modules. -/
theorem hasVanishingH1_iff_forall_qcoh {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] :
    HasVanishingH1 X ↔
      ∀ (F : QCoh X), IsZero (cohomology X ((QCoh.inclusion X).obj F) 1) :=
  sorry

/-- Affine algebraic spaces have vanishing first cohomology for quasi-coherent modules. -/
instance instHasVanishingH1_of_isAffine {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [IsAffine X] : HasVanishingH1 X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
