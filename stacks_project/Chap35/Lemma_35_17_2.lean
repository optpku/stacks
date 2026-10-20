module

import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.Syntomic
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.17.2: Cohen–Macaulayness is local for the syntomic precoverage. -/
@[stacks 036B] #check
  (AlgebraicGeometry.Scheme.CohenMacaulay.isLocalSyntomic :
    CategoryTheory.ObjectProperty.IsLocal
      (AlgebraicGeometry.Scheme.CohenMacaulay :
        CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage)
