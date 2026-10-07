module

import ReasLib.CategoryTheory.Homology.DoubleComplex.Dual
import StacksCheckRecall

@[expose] public section

open CategoryTheory ComplexShape

universe u

/- Remark 57.3.4. Let `K` be a finite-dimensional k-linear matress. Its oppositely indexed termwise dual is a matress with the canonical signed dual period. -/
@[stacks 0H8C] #check (HomologicalComplex₂.ModuleMatress.dualMatress :
  ∀ {k : Type u} [Field k]
    (K : HomologicalComplex₂ (ModuleCat.{u} k) (up ℤ) (up ℤ))
    (period : K ≅ K.bidegreeShift 3 (-3))
    [∀ p q : ℤ, FiniteDimensional k ((K.X p).X q)],
    HomologicalComplex₂.ModuleMatress K period →
      HomologicalComplex₂.ModuleMatress
        (HomologicalComplex₂.dualComplex K)
        (HomologicalComplex₂.ModuleMatress.dualPeriodIso K period))

end
