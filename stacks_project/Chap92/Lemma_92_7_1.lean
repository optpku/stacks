/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap92.Lemma_92_7_1_Omega
public import stacks_project.Chap92.Lemma_92_7_1_Sequence
import StacksCheckRecall

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

/- Lemma 92.7.1. With notation as in (92.7.0.2), the canonical sequence
0 → g₁⁻¹Ω₁ ⊗_B C → g₂⁻¹Ω₂ → g₃⁻¹Ω₃ → 0
of sheaves of C-modules on the polynomial-square site is short exact. -/
@[stacks 08QU] #check (Algebra.PolynomialTower.omegaSheafSequence_shortExact A B C :
  (Algebra.PolynomialTower.omegaSheafSequence A B C).ShortExact)

end RingedSite.Cotangent.PolynomialTriple
