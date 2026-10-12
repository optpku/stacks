/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.Ideal.HilbertSamuel.Multiplicity

universe u v

/- Definition 43.15.1 (1): at every degree at least `Module.supportDim R M`,
degree-`d` multiplicity is zero above the support dimension and is `d!` times the leading
coefficient of the Hilbert--Samuel `χ`-polynomial in the top degree. -/
@[stacks 0AZV] #check (Ideal.HilbertSamuel.multiplicityInDegree_spec :
  {R : Type u} → [CommRing R] → [IsLocalRing R] → [IsNoetherianRing R] →
    {M : Type v} → [AddCommGroup M] → [Module R M] → [Module.Finite R M] →
      (I : Ideal R) → I.IsIdealOfDefinition → (d : ℕ) →
        Module.supportDim R M ≤ d →
          Ideal.HilbertSamuel.multiplicityInDegree I M d =
            if Module.supportDim R M < d then 0
            else (d.factorial : ℚ) * (Ideal.HilbertSamuel.chiPolynomial I M).leadingCoeff)

/- Definition 43.15.1 (2): the unindexed multiplicity of `M` for an ideal of definition `I`
is its degree-`d` multiplicity when `d = Module.supportDim R M`. -/
@[stacks 0AZV]
#check (Ideal.HilbertSamuel.multiplicity_eq_multiplicityInDegree_of_supportDim_eq :
  {R : Type u} → [CommRing R] → [IsLocalRing R] → [IsNoetherianRing R] →
    {M : Type v} → [AddCommGroup M] → [Module R M] → [Module.Finite R M] →
      (I : Ideal R) → I.IsIdealOfDefinition → (d : ℕ) →
        Module.supportDim R M = d →
          Ideal.HilbertSamuel.multiplicity I M =
            Ideal.HilbertSamuel.multiplicityInDegree I M d)
