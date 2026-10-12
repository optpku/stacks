/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Sheaf
public import ReasLib.CategoryTheory.Sites.Localization.Representable
import StacksCheckRecall

/-!
# Lemma 18.21.3

Compatibility facade for representable localization.  Both site
presentations are compared with the same slice topos, and the ringed
structure map uses the standard slice-site owner.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology

/- Lemma 18.21.3 (04J3): the category-of-elements presentation at a
sheafified representable is compared with the slice topos. -/
@[stacks 04J3 "category-of-elements comparison"]
#check @sheafCategoryOfElementsEquivOver

/- The slice-site presentation is compared with the same slice topos. -/
@[stacks 04J3 "representable comparison"]
#check @GrothendieckTopology.RepresentableLocalization.comparison

@[stacks 04J3 "representable equivalence"]
#check @GrothendieckTopology.RepresentableLocalization.comparison.isEquivalence

#check @GrothendieckTopology.RepresentableLocalization.comparison.forget

/- On structure rings, representable localization is restriction to the
slice site and its canonical structure map. -/
@[stacks 04J3 "structure map"]
#check @RingedSite.Localization.AtSheaf.representableStructureMap

#check @SheafOfModules.overPushforwardOverAdj
