/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Exact
public import stacks_project.Chap43.Definition_43_15_1_AlgebraicMultiplicity

@[expose] public section

open CategoryTheory

universe u v

namespace Ideal.HilbertSamuel

section Local

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace ShortExact

variable {S : ShortComplex (ModuleCat.{v} R)}

/- The shared Hilbert--Samuel multiplicity additivity theorem for short exact sequences. -/
#check (Ideal.HilbertSamuel.ShortExact.multiplicity_eq_add :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      {S : ShortComplex (ModuleCat.{v} R)}
      [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
      (I : Ideal R) (hI : I.IsIdealOfDefinition) (hS : S.ShortExact)
      (d : ℕ) (hd : Module.supportDim R S.X₂ ≤ d),
      Ideal.HilbertSamuel.multiplicityInDegree I S.X₂ d =
        Ideal.HilbertSamuel.multiplicityInDegree I S.X₁ d +
          Ideal.HilbertSamuel.multiplicityInDegree I S.X₃ d)

end ShortExact

end Local

end Ideal.HilbertSamuel
