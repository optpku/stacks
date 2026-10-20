/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.IrreducibleComponents.Maps
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.8.14

The reusable dense-fiber irreducibility criterion is owned by
`ReasLib.Topology.IrreducibleComponents.Maps`.
-/

/- Lemma 5.8.14: dense irreducible fibers of an open map over an irreducible target give an
irreducible source. -/
@[stacks 004Z]
#check @IsOpenMap.irreducibleSpace_of_dense_irreducibleFibers
