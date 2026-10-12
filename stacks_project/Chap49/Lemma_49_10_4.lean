/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Syntomic

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 49.10.4: for a morphism of locally Noetherian schemes satisfying the equivalent
conditions of Lemma 49.10.1, the relative dualizing sheaf is an invertible module. -/
@[stacks 0BWF] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.invertibleOfLocallyQuasiFiniteSyntomic :
    ∀ {X Y : Scheme.{u}} {f : Y ⟶ X} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
      [LocallyQuasiFinite f] [Syntomic f] (W : f.RelativeDualizingSheaf),
      Scheme.Modules.Invertible W.module.obj)
