/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pullback of perfect derived modules on ringed sites

Perfectness is preserved by the canonical total derived pullback.  The statement is formulated
for bundled ringed sites and depends only on the instances needed to define that pullback.
-/

open CategoryTheory
open RingedSite.Hom (ModuleDerived ModuleQis modulePullbackDerived modulePullbackToDerived)

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom

section

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [∀ U : X,
  HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : Y,
  HasWeakSheafify (Y.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : Y,
  (Y.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (f : RingedSite.Hom X Y) [(f.modulePushforward.{w}).IsRightAdjoint]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{w} f) (ModuleQis.{w} Y)]

/-- Lemma 21.47.5: derived pullback along a morphism of ringed sites preserves perfect
derived module sheaves. -/
@[stacks 08H6]
theorem modulePullbackDerived_isPerfect
    (E : ModuleDerived.{w} Y) (hE : E.IsPerfect) :
    ((modulePullbackDerived.{w} f).obj E).IsPerfect := sorry

/-- Derived pullback restricted to the full subcategories of perfect derived module sheaves. -/
@[stacks 08H6 "perfect pullback functor"]
noncomputable def modulePullbackPerfect :
    ModuleDerived.Perfect (X := Y) ⥤ ModuleDerived.Perfect (X := X) :=
  ObjectProperty.FullSubcategory.restrict
    (P := ModuleDerived.perfect (X := Y))
    (Q := ModuleDerived.perfect (X := X))
    (modulePullbackDerived.{w} f)
    (modulePullbackDerived_isPerfect (X := X) (Y := Y) f)

/-- After forgetting perfectness, `modulePullbackPerfect` is the ordinary derived pullback. -/
@[stacks 08H6 "perfect pullback inclusion comparison"]
noncomputable def modulePullbackPerfectCompιIso :
    modulePullbackPerfect (X := X) (Y := Y) f ⋙
        ModuleDerived.Perfect.ι (X := X) ≅
      ModuleDerived.Perfect.ι (X := Y) ⋙ modulePullbackDerived.{w} f :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (P := ModuleDerived.perfect (X := Y))
    (Q := ModuleDerived.perfect (X := X))
    (modulePullbackDerived.{w} f)
    (modulePullbackDerived_isPerfect (X := X) (Y := Y) f)

end

end RingedSite.Hom
