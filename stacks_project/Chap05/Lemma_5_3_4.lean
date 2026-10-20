/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Maps.Equalizer
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.3.4

The product equality-locus theorem is owned by `ReasLib.Topology.Maps.Equalizer`.
-/

/- Lemma 5.3.4: the equality locus of continuous maps from two spaces to a Hausdorff target is
closed in their product. -/
@[stacks 08ZH]
#check Continuous.isClosed_eqLocus_prod
