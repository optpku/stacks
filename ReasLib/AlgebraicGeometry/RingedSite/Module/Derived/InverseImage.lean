/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.InverseImage.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.Functor.Derived.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived module inverse image from a site presentation

A continuous functor of sites presents module inverse image without requiring the additional
representable-flatness data of a bundled `RingedSite.Hom`.  Under cocontinuity this functor is
exact, hence acts canonically on derived categories.  This file separates that canonical action
from the total-right-derived model used to construct and compare derived adjunctions.
-/

@[expose] public section

-- The named ringed-site models unfold to this standard quotient; infer it
-- directly when the site is hidden behind a localized/source ModuleCat alias.
-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard

open CategoryTheory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
open ComplexShape

noncomputable section

universe z uC vC uD vD w

namespace RingedSite.Cocontinuous.moduleInverseImage

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The homotopy-to-derived functor induced by module inverse image in a continuous site
presentation. -/
@[stacks 0DD8 "continuous module inverse-image model"]
noncomputable abbrev toDerived
    (f : C ⥤ D) [f.IsContinuous J K] (R : Sheaf K RingCat.{w})
    [UnivLE.{max uC vC, z}] :
    RingedSite.Hom.ModuleHomotopy.{z} (target (K := K) R) ⥤
      RingedSite.Hom.ModuleDerived.{z} (source (J := J) (K := K) f R) :=
  (RingedSite.Cocontinuous.moduleInverseImage
      (J := J) (K := K) f R).mapHomotopyCategory (up ℤ) ⋙
    RingedSite.Hom.moduleLocalization (source (J := J) (K := K) f R)

/-- The canonical derived module inverse image induced by exactness. -/
@[stacks 07AC "derived module inverse image"]
noncomputable abbrev derived
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w})
    [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}] :
    RingedSite.Hom.ModuleDerived.{z} (target (K := K) R) ⥤
      RingedSite.Hom.ModuleDerived.{z} (source (J := J) (K := K) f R) :=
  letI := RingedSite.Hom.moduleCat_hasDerivedCategory (target (K := K) R)
  (exactFunctor (J := J) (K := K) f R).mapDerivedCategory

namespace toDerived

/-- The continuous-presentation inverse image has a total right-derived functor.  This named
bridge exposes the generic exact-functor instance through the site-presentation spelling used by
derived adjunctions. -/
@[stacks 07AC "derived inverse-image existence", instance]
theorem hasRightDerived
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w})
    [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}] :
    Functor.HasRightDerivedFunctor
      (moduleInverseImage.toDerived (J := J) (K := K) f R)
      (RingedSite.Hom.ModuleQis.{z} (target (K := K) R)) := sorry

end toDerived

/-- The total-right-derived model of module inverse image used by the derived-adjunction
construction. -/
@[stacks 07AC "total derived module inverse-image model"]
noncomputable abbrev totalDerived
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w})
    [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}] :
    RingedSite.Hom.ModuleDerived.{z} (target (K := K) R) ⥤
      RingedSite.Hom.ModuleDerived.{z} (source (J := J) (K := K) f R) :=
  letI := RingedSite.Hom.moduleCat_hasDerivedCategory (target (K := K) R)
  Functor.totalRightDerived
    (toDerived (J := J) (K := K) f R)
    (RingedSite.Hom.moduleLocalization (target (K := K) R))
    (RingedSite.Hom.ModuleQis.{z} (target (K := K) R))

namespace derived

/-- The exact derived inverse image carries its canonical right-derived-functor certificate in
the continuous ring-sheaf presentation. -/
@[stacks 07AC "exact inverse-image derived certificate", instance]
theorem isRightDerived
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w})
    [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}] :
    (derived (J := J) (K := K) f R).IsRightDerivedFunctor
      ((exactFunctor (J := J) (K := K) f R).obj.mapDerivedCategoryFactorsh.inv)
      (RingedSite.Hom.ModuleQis.{z} (target (K := K) R)) := sorry

end derived

/-- The total-right-derived model agrees canonically with the exact derived inverse image. -/
@[stacks 07AC "total-to-exact derived inverse-image comparison"]
noncomputable def totalDerivedIso
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w})
    [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}] :
    totalDerived (J := J) (K := K) f R ≅
      derived (J := J) (K := K) f R :=
  letI := RingedSite.Hom.moduleCat_hasDerivedCategory (target (K := K) R)
  Functor.rightDerivedNatIso
    (totalDerived (J := J) (K := K) f R)
    (derived (J := J) (K := K) f R)
    ((toDerived (J := J) (K := K) f R).totalRightDerivedUnit
      (RingedSite.Hom.moduleLocalization (target (K := K) R))
      (RingedSite.Hom.ModuleQis.{z} (target (K := K) R)))
    ((exactFunctor (J := J) (K := K) f R).obj.mapDerivedCategoryFactorsh.inv)
    (RingedSite.Hom.ModuleQis.{z} (target (K := K) R))
    (Iso.refl _)

end RingedSite.Cocontinuous.moduleInverseImage
