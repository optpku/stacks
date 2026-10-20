/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.KaehlerDifferent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 49.12.3: for a morphism `f : Y ⟶ X` of Noetherian schemes satisfying the
equivalent conditions of Lemma 49.10.1 (locally quasi-finite and syntomic), the
different of `f` associated to a relative dualizing sheaf and a trace section is
the Kähler different of `f`. -/
@[stacks 0BWG] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.different_eq_kaehlerDifferent :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsNoetherian X] [IsNoetherian Y]
      [LocallyQuasiFinite f] [Syntomic f] (W : f.RelativeDualizingSheaf)
      (τ : W.module.obj.sections) (hτ : W.IsTraceSection τ),
      W.different τ = f.kaehlerDifferent)
