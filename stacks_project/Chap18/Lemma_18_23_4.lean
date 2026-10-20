/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.LocalGeneration
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.LocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.Quasicoherent
import StacksCheckRecall

/-!
# Lemma 18.23.4

Source facade for the property-specific inverse-image API.  The reusable
statements hold for arbitrary sheaves of rings and are split by property under
`Sheaf/PullbackContinuous/` in namespace `SheafOfModules`; the chapter file
introduces no local instances.
-/

@[expose] public section

/- Lemma 18.23.4 (1) (03DO): inverse image preserves local freeness. -/
@[stacks 03DO "(1)"]
#check @SheafOfModules.pullback_isLocallyFree

/- Lemma 18.23.4 (2) (03DO): inverse image preserves finite local freeness. -/
@[stacks 03DO "(2)"]
#check @SheafOfModules.pullback_isFiniteLocallyFree

/- Lemma 18.23.4 (3) (03DO): inverse image preserves local generation by sections. -/
@[stacks 03DO "(3)"]
#check @SheafOfModules.pullback_isLocallyGeneratedBySections

/- Lemma 18.23.4 (4) (03DO): inverse image preserves local generation by `r` sections. -/
@[stacks 03DO "(4)"]
#check @SheafOfModules.pullback_isLocallyGeneratedBy

/- Lemma 18.23.4 (5) (03DO): inverse image preserves finite type. -/
@[stacks 03DO "(5)"]
#check @SheafOfModules.pullback_isFiniteType

/- Lemma 18.23.4 (6) (03DO): inverse image preserves quasi-coherence. -/
@[stacks 03DO "(6)"]
#check @SheafOfModules.pullback_isQuasicoherent

/- Lemma 18.23.4 (7) (03DO): inverse image preserves finite presentation. -/
@[stacks 03DO "(7)"]
#check @SheafOfModules.pullback_isFinitePresentation
