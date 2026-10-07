module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalProperties
import StacksCheckRecall

/-!
# Definition 18.23.1

The common local properties remain owned by Mathlib.  ReasLib supplies only
the finite-local-free, fixed-generator, and coherence refinements missing
there, all over an arbitrary sheaf of rings.
-/

@[expose] public section

open SheafOfModules

/- Definition 18.23.1 (1) (03DL): Mathlib local freeness. -/
@[stacks 03DL "(1)"]
#check @SheafOfModules.IsLocallyFree

/- Definition 18.23.1 (2) (03DL): finite local freeness. -/
@[stacks 03DL "(2)"]
#check @SheafOfModules.IsFiniteLocallyFree

/- Definition 18.23.1 (3) (03DL): local generation by sections. -/
@[stacks 03DL "(3)"]
#check @IsLocallyGeneratedBySections

/- Definition 18.23.1 (4) (03DL): local generation by `r` sections. -/
@[stacks 03DL "(4)"]
#check @IsLocallyGeneratedBy

/- Definition 18.23.1 (5) (03DL): Mathlib finite type. -/
@[stacks 03DL "(5)"]
#check @SheafOfModules.IsFiniteType

/- Definition 18.23.1 (6) (03DL): Mathlib quasi-coherence. -/
@[stacks 03DL "(6)"]
#check @SheafOfModules.IsQuasicoherent

/- Definition 18.23.1 (7) (03DL): Mathlib finite presentation. -/
@[stacks 03DL "(7)"]
#check @SheafOfModules.IsFinitePresentation

/- Definition 18.23.1 (8) (03DL): coherence. -/
@[stacks 03DL "(8)"]
#check @SheafOfModules.IsCoherent
