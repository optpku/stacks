/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Hom.Boundary
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.EulerCharacteristic
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ShortExact

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism.Hom

variable {R : Type u} [Ring R]
variable {K L : TwoPeriodicEndomorphism (ModuleCat.{v} R)}

/-- A morphism of two-periodic complexes with finite-length source and target cohomology,
kernel, and cokernel preserves multiplicity. -/
theorem multiplicity_eq (f : Hom K L)
    (hK₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (hK₁ : IsFiniteLength R (K.toCochainComplex.homology 1))
    (hL₀ : IsFiniteLength R (L.toCochainComplex.homology 0))
    (hL₁ : IsFiniteLength R (L.toCochainComplex.homology 1))
    (hker : IsFiniteLength R (kernel f.hom : ModuleCat.{v} R))
    (hcoker : IsFiniteLength R (cokernel f.hom : ModuleCat.{v} R)) :
    K.multiplicity hK₀ hK₁ = L.multiplicity hL₀ hL₁ := sorry

end CategoryTheory.TwoPeriodicEndomorphism.Hom
