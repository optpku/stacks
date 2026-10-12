/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.MeromorphicSection
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import StacksCheckRecall

/-!
# Definition 31.23.3

The reusable meromorphic-section API is owned by
`ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.MeromorphicSection`.

@stack 01X4
-/

@[expose] public section

universe u

/- Definition 31.23.3

For a locally ringed space `X` and an `𝒪_X`-module sheaf `ℱ`, the sheaf of meromorphic sections
is obtained by extending scalars from `𝒪_X` to the sheaf `𝒦_X` of meromorphic functions.
-/
@[stacks 01X4]
#check
  (AlgebraicGeometry.LocallyRingedSpace.meromorphicSectionSheaf :
    (X : AlgebraicGeometry.LocallyRingedSpace.{u}) →
      SheafOfModules.RingedSite.ringedSiteModuleCategory
          (Opens.grothendieckTopology X.toTopCat) X.𝒪 →
        SheafOfModules.RingedSite.ringedSiteModuleCategory
          (Opens.grothendieckTopology X.toTopCat)
          (AlgebraicGeometry.LocallyRingedSpace.meromorphicFunctionSheaf X))

#check
  (AlgebraicGeometry.LocallyRingedSpace.meromorphicSectionSheaf_eq_pullback :
    (X : AlgebraicGeometry.LocallyRingedSpace.{u}) →
      (ℱ : SheafOfModules.RingedSite.ringedSiteModuleCategory
        (Opens.grothendieckTopology X.toTopCat) X.𝒪) →
      AlgebraicGeometry.LocallyRingedSpace.meromorphicSectionSheaf X ℱ =
        (SheafOfModules.pullback.{u}
          (AlgebraicGeometry.LocallyRingedSpace.toMeromorphicFunctionRingSheafMap X)).obj ℱ)

#check
  (AlgebraicGeometry.LocallyRingedSpace.meromorphicSections_eq_sections :
    (X : AlgebraicGeometry.LocallyRingedSpace.{u}) →
      (ℱ : SheafOfModules.RingedSite.ringedSiteModuleCategory
        (Opens.grothendieckTopology X.toTopCat) X.𝒪) →
      AlgebraicGeometry.LocallyRingedSpace.meromorphicSections X ℱ =
        (AlgebraicGeometry.LocallyRingedSpace.meromorphicSectionSheaf X ℱ).sections)
