/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Catenary
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.11.5

The reusable locality and locally-closed transport API for catenary spaces is owned by
`ReasLib.Topology.Catenary`.
-/

/- Lemma 5.11.5 (1): catenarity is local for open coverings. -/
@[stacks 02I2 "catenarity is local for an open covering"]
#check @TopologicalSpace.catenarySpace_iff_hasOpenCoverByCatenarySpaces

/- Lemma 5.11.5 (2): locally closed subspaces of catenary spaces are catenary. -/
@[stacks 02I2 "locally closed subspaces of catenary spaces are catenary"]
#check @IsLocallyClosed.catenarySpace
