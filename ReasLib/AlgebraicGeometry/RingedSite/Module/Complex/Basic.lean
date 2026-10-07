module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic

@[expose] public section

/-!
# Homology structures for complexes of modules on ringed sites

The abelian category of module sheaves carries canonical homology data. This file owns that data
below the derived-category layer so complex-level APIs can use it without a reverse dependency on
derived categories.
-/

open CategoryTheory
open SheafOfModules.RingedSite (ringedSiteModuleCategory)

noncomputable section

namespace RingedSite.ModuleCat

/-- Module sheaves on a ringed site carry the homology structure induced by their canonical
abelian structure. -/
theorem categoryWithHomology.{z, u, v, w}
    (X : RingedSite.{u, v, w}) [UnivLE.{max u v, z}] :
    CategoryWithHomology (ModuleCat.{z} X) :=
  CategoryTheory.categoryWithHomology_of_abelian

/-- Module sheaves on a localized ringed site inherit the same canonical homology structure. -/
theorem localizationCategoryWithHomology.{z, u, v, w}
    (X : RingedSite.{u, v, w}) (U : X) [UnivLE.{max u v, z}] :
    CategoryWithHomology (ModuleCat.{z} (X.localization U)) :=
  categoryWithHomology (X.localization U)

end RingedSite.ModuleCat

universe u v w z

namespace RingedSite.CommRingPresentation

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (O : Sheaf J CommRingCat.{w}) [UnivLE.{max u v, z}]

/-- The canonical homology structure on modules over a commutative ring-sheaf presentation. -/
@[stacks 03CW "commutative ringed-site homology presentation"]
theorem moduleCategoryWithHomology :
    CategoryWithHomology (ringedSiteModuleCategory.{u, v, z, w} J O) :=
  RingedSite.ModuleCat.categoryWithHomology
    (RingedSite.ofCommRingSheaf J O)

end RingedSite.CommRingPresentation
