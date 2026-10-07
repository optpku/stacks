module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Localization
public import ReasLib.Algebra.Homology.DerivedCategory.InjectiveModel
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology.Dimension
public import ReasLib.CategoryTheory.Limits.Coproduct.Retract
public import ReasLib.CategoryTheory.Preadditive.CompactObject.Relative
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative compactness of localized generators on ringed sites

The extension `j_!𝒪_U`, placed in degree zero, is the canonical localized generator attached to
an object `U` of a ringed site.  When all cohomology functors over `U` commute with coproducts,
this generator is compact relative to ambient derived coproducts whose apex is bounded below.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

-- Local instance justification (defeq pin): use the standard derived-category model
-- already fixed explicitly by ModuleDerived and moduleLocalization.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

universe u v w

namespace RingedSite.Hom.ModuleDerived

/-- The localized structure module represented by `U`, placed in cohomological degree zero. -/
@[stacks 0G21 "localized generator in degree zero"]
noncomputable abbrev localizedGenerator
    (X : RingedSite.{u, v, w}) [UnivLE.{max u v, w}] (U : X)
    [(SheafOfModules.Localization.restriction X.structureSheaf U :
      RingedSite.ModuleCat.{w} X ⥤
        SheafOfModules.{w} (X.structureSheaf.over U)).IsRightAdjoint] :
    ModuleDerived.{w} X :=
  (DerivedCategory.singleFunctor (RingedSite.ModuleCat.{w} X) (0 : ℤ)).obj
    (SheafOfModules.Localization.structureModule X.structureSheaf U)

namespace LocalizedGenerator

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [IsGrothendieckAbelian.{w} (RingedSite.ModuleCat.{w} X)]

/-- Lemma 21.52.3 (0G21): if cohomology over `U` commutes with coproducts, then
`j_!𝒪_U[0]` is compact relative to derived coproducts whose coproduct object is bounded below. -/
@[stacks 0G21]
theorem isCompactOnBoundedBelow (U : X)
    [(SheafOfModules.Localization.restriction X.structureSheaf U :
      RingedSite.ModuleCat.{w} X ⥤
        SheafOfModules.{w} (X.structureSheaf.over U)).IsRightAdjoint]
    (hU : ModuleCohomology.PreservesCoproducts X U) :
    IsCompactObjectOn
      (t.plus : ObjectProperty (ModuleDerived.{w} X))
      (localizedGenerator X U) := sorry

end LocalizedGenerator

end RingedSite.Hom.ModuleDerived

end
