/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.BasicOpen
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.6.2: basic-open membership is detected in the local ring, and the
defining section becomes a unit on that open. -/
@[stacks 01HZ] #check LocallyRingedSpace.mem_basicOpen_top_iff_notMem_maximalIdeal
@[stacks 01HZ] #check RingedSpace.isUnit_res_basicOpen

/- The arbitrary-open version is the reusable generalization of the source statement. -/
#check LocallyRingedSpace.mem_basicOpen_iff_notMem_maximalIdeal
