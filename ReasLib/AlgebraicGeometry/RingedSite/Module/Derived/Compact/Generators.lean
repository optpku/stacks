module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Generators
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Compact
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Compact.Generators
public import ReasLib.CategoryTheory.Sites.EnoughObjects
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-compact generators for derived module categories

The localized structure modules represented by quasi-compact objects form the canonical
generating family used to describe compact objects of a ringed-site derived category.
-/

@[expose] public section

open CategoryTheory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
open CategoryTheory.ObjectProperty

noncomputable section

universe g w v u

namespace RingedSite.ModuleCat

variable (X : RingedSite.{u, v, w}) [UnivLE.{max u v, w}]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{w}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X, (SheafOfModules.Localization.restriction X.structureSheaf U :
  RingedSite.ModuleCat.{w} X ⥤
    SheafOfModules.{w} (X.structureSheaf.over U)).IsRightAdjoint]

/-- Modules isomorphic to the localized structure module represented by a quasi-compact
object of a ringed site. -/
@[stacks 094C "quasi-compact generator property"]
def quasiCompactGenerators : ObjectProperty (RingedSite.ModuleCat.{w} X) :=
  fun M ↦ ∃ U : X, X.siteTopology.QuasiCompactObject U ∧
    Nonempty (SheafOfModules.Localization.structureModule X.structureSheaf U ≅ M)

namespace QuasiCompactGenerators

omit [HasWeakSheafify X.siteTopology AddCommGrpCat.{w}]
  [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Membership means being isomorphic to the localized structure module of a quasi-compact
site object. -/
@[stacks 094C "membership"]
theorem mem_iff (M : RingedSite.ModuleCat.{w} X) :
    quasiCompactGenerators X M ↔
      ∃ U : X, X.siteTopology.QuasiCompactObject U ∧
        Nonempty (SheafOfModules.Localization.structureModule X.structureSheaf U ≅ M) := sorry

omit [HasWeakSheafify X.siteTopology AddCommGrpCat.{w}]
  [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The localized structure module represented by a quasi-compact object belongs to the
canonical generating family. -/
@[stacks 094C "standard generator"]
theorem structureModule_mem {U : X} (hU : X.siteTopology.QuasiCompactObject U) :
    quasiCompactGenerators X
      (SheafOfModules.Localization.structureModule X.structureSheaf U) := sorry

/-- Every member of the quasi-compact localized generating family is compact. -/
@[stacks 094C "compact generators"]
theorem isCompactObject {M : RingedSite.ModuleCat.{w} X}
    (hM : quasiCompactGenerators X M) : CategoryTheory.IsCompactObject M := sorry

/-- If quasi-compact objects cover the site, the corresponding localized structure modules
form a separating family of module sheaves. -/
@[stacks 094C "separating family"]
theorem isSeparating
    (hEnough : X.siteTopology.HasEnoughObjectsWithProperty
      X.siteTopology.QuasiCompactObject) :
    (quasiCompactGenerators X).IsSeparating := sorry

variable [IsGrothendieckAbelian.{g} (RingedSite.ModuleCat.{w} X)]

/-- Lemma 21.52.2 (094C): if every object of a ringed site is covered by quasi-compact
objects, every compact object of its module-derived category is a retract of the image of a
bounded complex whose terms are finite sums of quasi-compact localized structure modules. -/
@[stacks 094C]
theorem exists_retract_bounded
    (hEnough : X.siteTopology.HasEnoughObjectsWithProperty
      X.siteTopology.QuasiCompactObject)
    {K : RingedSite.Hom.ModuleDerived.{w} X} (hK : CategoryTheory.IsCompactObject K) :
    ∃ L : CochainComplex.Bounded (RingedSite.ModuleCat.{w} X),
      (∀ i : ℤ, (quasiCompactGenerators X).additiveClosure (L.obj.X i)) ∧
        Nonempty (Retract K (DerivedCategory.Q.obj L.obj)) := sorry

end QuasiCompactGenerators

end RingedSite.ModuleCat
