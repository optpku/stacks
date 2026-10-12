/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.FiniteFlatTrace

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 49.15.2 -/
@[stacks 0BVI]
#check (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.traceSection_eq_adjointTrace :
  ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsNoetherian X] [IsNoetherian Y] [IsFinite f] [Flat f]
    (W : f.RelativeDualizingSheaf)
    (hW : RingedSpace.ModuleDerived.cohomologySheaf
        ((AlgebraicGeometry.Scheme.DerivedQCoh.finiteRightAdjoint f).obj
          (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf X)).obj 0 =
      W.module.obj)
    (tau : W.module.obj.sections)
    (h_tau : W.IsTraceSection tau),
    SheafOfModules.sectionsMap (eqToIso hW).hom
        (AlgebraicGeometry.Scheme.DerivedQCoh.adjointTraceSection f W hW) =
      tau)
