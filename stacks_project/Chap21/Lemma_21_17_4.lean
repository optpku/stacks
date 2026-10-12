/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Localization.KFlat
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.17.4

The K-flatness statement for restriction to a localized ringed site is owned by the reusable
localization-complex API in ReasLib.
-/

/- Lemma 21.17.4 (0E8K): restriction to a localized ringed site preserves K-flat cochain
complexes. -/
@[stacks 0E8K]
#check @SheafOfModules.RingedSite.CochainComplex.IsKFlat.localizedRestriction

#check @RingedSite.Hom.localizedRestrictionComplex
