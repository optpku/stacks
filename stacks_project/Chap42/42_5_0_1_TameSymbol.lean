/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.Finite
public import ReasLib.RingTheory.LocalRing.TameSymbol.Factorization

universe u v

open IsLocalRing
open scoped BigOperators

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing B] [Algebra A B] [Module.Finite A B]
variable {a₁ a₂ : A}

/- The compatibility import exposes the complete explicit norm-product formula. -/
#check (TameSymbol.Factorization.value_def :
  (D : TameSymbol.Factorization A B a₁ a₂) →
    D.value =
      D.maximals.prod fun j ↦
        (TameSymbol.residueNorm A j (D.liesOver j)
          ((-1 : j.asIdeal.ResidueFieldˣ) ^ (D.e₁ j * D.e₂ j) *
            Units.map (IsLocalRing.residue (Localization.AtPrime j.asIdeal)).toMonoidHom
                (D.u₁ j) ^ D.e₂ j *
            Units.map (IsLocalRing.residue (Localization.AtPrime j.asIdeal)).toMonoidHom
                (D.u₂ j) ⁻¹ ^ D.e₁ j)) ^ D.m j)

end
