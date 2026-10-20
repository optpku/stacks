/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InternalHom.Coherent
import StacksCheckRecall

/-!
# Internal Hom and coherent module sheaves

The local finite-kernel shape and its coherence consequence are reusable ReasLib declarations.
This file records only their ringed-space source specialization.
-/

@[expose] public section

/- Lemma 17.22.6 (01CQ), first clause: internal Hom from a finitely presented module sheaf is
locally a kernel between finite direct sums of copies of the target. -/
@[stacks 01CQ "local-kernel clause"]
#check @AlgebraicGeometry.RingedSpace.InternalHom.finiteKernelIsLocal

/- Lemma 17.22.6 (01CQ), second clause: a coherent target gives a coherent internal Hom. -/
@[stacks 01CQ "coherence clause"]
#check @AlgebraicGeometry.RingedSpace.InternalHom.isCoherent

/- The local-kernel shape is independently reusable beyond internal Hom. -/
#check @SheafOfModules.RingedSite.FiniteKernel.IsLocal
#check @SheafOfModules.RingedSite.FiniteKernel.IsLocal.isCoherent
