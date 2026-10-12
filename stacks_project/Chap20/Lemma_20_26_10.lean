/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.KFlat.Colimit

@[expose] public section

/- @stack 06YE -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/- Lemma 20.26.10 (06YE): the sequential colimit of K-flat complexes is K-flat. -/
@[stacks 06YE "sequential colimits preserve K-flatness"]
#check @AlgebraicGeometry.RingedSpace.CochainComplex.IsKFlat.sequentialColimit

#check @SheafOfModules.RingedSite.CochainComplex.IsKFlat.sequentialColimit

end
