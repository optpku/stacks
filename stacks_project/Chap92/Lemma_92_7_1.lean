module

public import stacks_project.Chap92.Lemma_92_7_1_Omega
public import stacks_project.Chap92.Lemma_92_7_1_Sequence
import Mathlib.Tactic.CrossRefAttribute

/-!
# The sheaf-level Jacobi–Zariski sequence on `C_{C/B/A}`

Lemma 92.7.1 produces a canonical short exact sequence of sheaves of `underline{C}`-modules
from the naive differentials `Ω₁`, `Ω₂`, `Ω₃` of (92.7.0.2).
-/

@[expose] public section

open CategoryTheory
open RingedSite.Cotangent.PolynomialTriple

noncomputable section

universe u

namespace RingedSite.Cotangent.PolynomialTriple

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- Lemma 92.7.1. With notation as in (92.7.0.2), set Ω₁ = omegaSheaf A B on C_{B/A},
Ω₂ = omegaSheaf A C on C_{C/A}, and Ω₃ = omegaSheaf B C on C_{C/B}. Then there is a
canonical short exact sequence of sheaves of underline{C}-modules
0 ⟶ g1⁻¹ Ω₁ ⊗_{underline{B}} underline{C} ⟶ g2⁻¹ Ω₂ ⟶ g3⁻¹ Ω₃ ⟶ 0
on C_{C/B/A}. -/
@[stacks 08QU]
theorem omegaSequence_shortExact : (omegaSequence A B C).ShortExact :=
  sorry

end RingedSite.Cotangent.PolynomialTriple
