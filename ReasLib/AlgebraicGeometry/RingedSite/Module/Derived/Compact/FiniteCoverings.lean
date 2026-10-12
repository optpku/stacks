/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Compact.LocalizedGenerator
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology.FiniteCoverings
import Mathlib.Tactic.CrossRefAttribute

/-!
# Compact localized generators from finite cofinal coverings

This bridge combines the coefficient-independent finite Cech covering theorem with the
relative compactness criterion for the degree-zero localized generator.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Sheaf.Cech.CofinalSystem
open DerivedCategory.TStructure

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived.LocalizedGenerator

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [IsGrothendieckAbelian.{w} (RingedSite.ModuleCat.{w} X)]
variable [∀ U : X, HasFiniteProducts (Over U)]
variable [HasSheafify X.siteTopology AddCommGrpCat.{w}]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat.{w})]

/-- Lemma 21.52.4 (0G22): a finite cofinal covering system makes the degree-zero localized
generator compact relative to bounded-below derived coproducts over every controlled object. -/
@[stacks 0G22]
theorem isCompactOnBoundedBelow_of_finiteCoverings
    (B : Set X)
    (Cov : ∀ U : X, Set (FormalCoproduct (Over U)))
    (hCov : FiniteCoverings X.siteTopology B Cov)
    {U : X} (hU : U ∈ B)
    [(SheafOfModules.Localization.restriction X.structureSheaf U :
      RingedSite.ModuleCat.{w} X ⥤
        SheafOfModules.{w} (X.structureSheaf.over U)).IsRightAdjoint] :
    IsCompactObjectOn
      (t.plus : ObjectProperty (ModuleDerived.{w} X))
      (localizedGenerator X U) := sorry

end RingedSite.Hom.ModuleDerived.LocalizedGenerator

end
