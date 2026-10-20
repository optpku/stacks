/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Pullback

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

section Pullback

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
variable [∀ x : X.total, HasWeakSheafify
    ((fppfTopology X).over x) AddCommGrpCat.{u}]
variable [∀ x : X.total,
    ((fppfTopology X).over x).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ y : Y.total, HasWeakSheafify
    ((fppfTopology Y).over y) AddCommGrpCat.{u}]
variable [∀ y : Y.total,
    ((fppfTopology Y).over y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Pullback along a morphism of categories fibred in groupoids over the big fppf site
preserves quasi-coherent sheaves of modules. -/
instance pullback_isQuasicoherent
    (F : SheafOfModules.{u} (structureSheaf Y))
    [F.IsQuasicoherent] :
    ((modulePullback f).obj F).IsQuasicoherent :=
  sorry

end Pullback

section Quasicoherent

variable {S : Scheme.{u}} (X : GroupoidsOver S)

/-- Abelian-group-valued sheaf composition exists on every slice of the fppf
ringed site of a category fibred in groupoids. -/
instance hasSheafCompose_fppfRingedSite_over :
    ∀ x, ((ringedSite X).siteTopology.over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Weak sheafification of abelian groups exists on every slice of the fppf
ringed site of a category fibred in groupoids. -/
instance hasWeakSheafify_fppfRingedSite_over :
    ∀ x, HasWeakSheafify ((ringedSite X).siteTopology.over x)
      AddCommGrpCat.{u} :=
  sorry

/-- Sheafification equivalences on slices of the fppf ringed site of a category
fibred in groupoids are exactly the locally bijective morphisms. -/
instance wEqualsLocallyBijective_fppfRingedSite_over :
    ∀ x, ((ringedSite X).siteTopology.over x).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  sorry

/-- The object property of quasi-coherent module sheaves on the fppf site of a
category fibred in groupoids. -/
abbrev quasiCoherentModuleProperty :
    ObjectProperty (SheafOfModules.{u} (structureSheaf X)) :=
  SheafOfModules.isQuasicoherent (structureSheaf X)

/-- Quasi-coherence is the site-level quasi-coherence predicate for the fppf
structure sheaf. -/
theorem quasiCoherentModuleProperty_eq :
    quasiCoherentModuleProperty X =
      SheafOfModules.isQuasicoherent (structureSheaf X) :=
  rfl

/-- A module sheaf on the fppf site satisfies the quasi-coherent object property
if and only if it is quasi-coherent. -/
theorem mem_QCoh_iff {M : SheafOfModules.{u} (structureSheaf X)} :
    quasiCoherentModuleProperty X M ↔ M.IsQuasicoherent :=
  Iff.rfl

/-- The category of quasi-coherent modules on the fppf ringed site of a
category fibred in groupoids. -/
abbrev QCoh :=
  (quasiCoherentModuleProperty X).FullSubcategory

namespace QCoh

/-- The inclusion of quasi-coherent modules into all module sheaves on the fppf
ringed site. -/
abbrev inclusion : QCoh X ⥤ SheafOfModules.{u} (structureSheaf X) :=
  (quasiCoherentModuleProperty X).ι

end QCoh

end Quasicoherent

end AlgebraicGeometry.GroupoidsOver
