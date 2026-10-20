/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.TraceSection

@[expose] public section

open AlgebraicGeometry SheafOfModules

universe u

/- Remark 49.4.7: a flat locally quasi-finite morphism of locally Noetherian schemes has a
global section of any chosen relative dualizing sheaf that maps to the trace element on
every compatible affine pair. -/
@[stacks 0BVJ] #check (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.exists_traceSection :
  ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [Flat f]
    (W : f.RelativeDualizingSheaf),
    ∃ τ : sections W.module.obj, W.IsTraceSection τ)
