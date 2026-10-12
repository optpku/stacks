/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback
import StacksCheckRecall

/-!
# Lemma 18.23.4

Compatibility facade for the property-specific inverse-image API.  The
reusable statements are split by property under
`SheafOfModules.RingedSite`; the chapter file introduces no local instances.
-/

@[expose] public section

/- Lemma 18.23.4 (1) (03DO): inverse image preserves local freeness. -/
@[stacks 03DO "(1)"]
#check @SheafOfModules.RingedSite.pullback_isLocallyFree

/- Lemma 18.23.4 (2) (03DO): inverse image preserves finite local freeness. -/
@[stacks 03DO "(2)"]
#check @SheafOfModules.RingedSite.pullback_isFiniteLocallyFree

/- Lemma 18.23.4 (3) (03DO): inverse image preserves local generation by sections. -/
@[stacks 03DO "(3)"]
#check @SheafOfModules.RingedSite.pullback_isLocallyGeneratedBySections

/- Lemma 18.23.4 (4) (03DO): inverse image preserves local generation by `r` sections. -/
@[stacks 03DO "(4)"]
#check @SheafOfModules.RingedSite.pullback_isLocallyGeneratedBy

/- Lemma 18.23.4 (5) (03DO): inverse image preserves finite type. -/
@[stacks 03DO "(5)"]
#check @SheafOfModules.RingedSite.pullback_isFiniteType

/- Lemma 18.23.4 (6) (03DO): inverse image preserves quasi-coherence. -/
@[stacks 03DO "(6)"]
#check @SheafOfModules.RingedSite.pullback_isQuasicoherent

/- Lemma 18.23.4 (7) (03DO): inverse image preserves finite presentation. -/
@[stacks 03DO "(7)"]
#check @SheafOfModules.RingedSite.pullback_isFinitePresentation
