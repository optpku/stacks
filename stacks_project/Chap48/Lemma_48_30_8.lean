module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealPower.Comparison

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 48.30.8: for a termwise coherent complex on a Noetherian scheme, the
cohomology tower of its termwise ideal-power subcomplexes and the ideal-power
tower of its ambient cohomology are isomorphic as pro-objects, via canonical
maps satisfying the stated stable-range image and composite formulas.
-/
@[stacks 0G4R] #check
  (AlgebraicGeometry.Scheme.Modules.IdealPowerCohomology.existsComparison :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
      (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ)
      [∀ i : ℤ, (K.X i).IsCoherent] (p : ℤ),
      ∃ c : ℕ, ∃ D : Scheme.Modules.IdealPowerCohomology.Comparison I K p c, 0 < c)

#check @Scheme.Modules.IdealPowerCohomology.Comparison.imageBound
#check @Scheme.Modules.IdealPowerCohomology.Comparison.reverseAt
#check @Scheme.Modules.IdealPowerCohomology.Comparison.reverse_forward
#check @Scheme.Modules.IdealPowerCohomology.Comparison.forward_reverse
#check @Scheme.Modules.IdealPowerCohomology.Comparison.toProIso
