module

public import ReasLib.Algebra.Module.DirectSumDevissage.Basic
import StacksCheckRecall

/-!
@stack 058U
-/

@[expose] public section

/- Definition 10.84.1: a direct sum devissage is an ordinal-indexed increasing family of
submodules starting at `⊥`, exhausting the module, continuous at limit ordinals, and whose
successor inclusions split. -/
@[stacks 058U]
#check @DirectSumDevissage

/- A Kaplansky devissage has countably generated quotients at all successor stages. -/
@[stacks 058U "Kaplansky devissage"]
#check @DirectSumDevissage.IsKaplansky
