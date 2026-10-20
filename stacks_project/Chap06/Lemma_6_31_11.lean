/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.ExtensionByInitial
import StacksCheckRecall

@[expose] public section

/- Lemma 6.31.11 (1): for sheaves valued in a category with an initial object, extension by the
initial object along an open inclusion is fully faithful. -/
@[stacks 00AA "extension by the initial object is fully faithful"]
recall TopCat.Sheaf.ExtensionByInitial.Properties.fullyFaithful

/- Lemma 6.31.11 (2): a sheaf lies in the essential image of extension by the initial object
from an open subset exactly when each stalk outside that subset is initial. -/
@[stacks 00AA "essential image characterized by initial stalks outside the open subset"]
recall TopCat.Sheaf.ExtensionByInitial.Properties.essImage_iff
