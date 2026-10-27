/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SpacesGrothendieck
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.NativeGlobalSections

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Degree-zero placement of a spaces-étale module in its native derived category. -/
def spacesEtaleModuleSingleFunctor (Y : AlgebraicSpace S) :
    RingedSite.ModuleCat.{u} (spacesRingedSite Y) ⥤
      RingedSite.NativeDerived.category.{u} (spacesRingedSite Y) :=
  HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{u} (spacesRingedSite Y)) 0 ⋙
    RingedSite.NativeDerived.localization.{u} (spacesRingedSite Y)

/-- A spaces-étale module regarded as a derived object concentrated in degree zero. -/
def spacesEtaleModuleSingle (Y : AlgebraicSpace S)
    (F : RingedSite.ModuleCat.{u} (spacesRingedSite Y)) :
    RingedSite.NativeDerived.category.{u} (spacesRingedSite Y) :=
  (spacesEtaleModuleSingleFunctor Y).obj F

/-- Spaces-étale module cohomology, functorially in the coefficient module. -/
def spacesEtaleModuleCohomologyFunctor (Y : AlgebraicSpace S) (q : ℕ) :
    RingedSite.ModuleCat.{u} (spacesRingedSite Y) ⥤ AddCommGrpCat.{u + 1} :=
  spacesEtaleModuleSingleFunctor Y ⋙
    RingedSite.ToposHom.NativeDerived.derivedGlobalSections (spacesRingedSite Y) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)

/-- The degree-`q` spaces-étale cohomology group of a module. -/
abbrev spacesEtaleModuleCohomology (Y : AlgebraicSpace S)
    (F : RingedSite.ModuleCat.{u} (spacesRingedSite Y)) (q : ℕ) :
    AddCommGrpCat.{u + 1} :=
  (spacesEtaleModuleCohomologyFunctor Y q).obj F

/-- Module cohomology is homology of native derived global sections of the module
placed in degree zero. -/
theorem spacesEtaleModuleCohomology_eq (Y : AlgebraicSpace S)
    (F : RingedSite.ModuleCat.{u} (spacesRingedSite Y)) (q : ℕ) :
    spacesEtaleModuleCohomology Y F q =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
        ((RingedSite.ToposHom.NativeDerived.derivedGlobalSections (spacesRingedSite Y)).obj
          (spacesEtaleModuleSingle Y F)) := rfl

end AlgebraicGeometry.AlgebraicSpace
