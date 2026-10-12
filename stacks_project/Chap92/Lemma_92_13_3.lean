/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_13_3_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison of the cotangent complex with the Lichtenbaum–Schlessinger complex

Lemma 92.13.3 records the canonical cochain map `L_{B/A} ⟶ L` of a polynomial
presentation, identifying the Lichtenbaum–Schlessinger complex with the good
truncation `τ_{≥ -2} L_{B/A}`.
-/

@[expose] public section

open Algebra.Presentation
open Algebra.Presentation.LichtenbaumSchlessinger
open HomologicalComplex

universe u

noncomputable section

namespace Algebra.Presentation.LichtenbaumSchlessinger

variable {A B ι σ : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Lemma 92.13.3 (1) In the situation above denote `L` the complex (92.13.0.1).
There is a canonical map `L_{B/A} ⟶ L` in `D(B)`, represented by the cochain
map `toComplex` from `Algebra.cotangentComplex A B` to `complex P`. -/
@[stacks 09CG]
abbrev toLichtenbaumSchlessinger (P : Presentation A B ι σ) :
    Algebra.cotangentComplex A B ⟶ complex P :=
  toComplex P

/-- Unfolding of the source-facing comparison recovers `toComplex`. -/
theorem toLichtenbaumSchlessinger_eq (P : Presentation A B ι σ) :
    toLichtenbaumSchlessinger P = toComplex P := sorry

/-- Lemma 92.13.3 (2) The canonical map induces an isomorphism
`τ_{≥ -2} L_{B/A} ⟶ L` in `D(B)`. -/
@[stacks 09CG]
instance toLichtenbaumSchlessinger_truncGE_quasiIso (P : Presentation A B ι σ) :
    QuasiIso (CochainComplex.truncGEMap (toLichtenbaumSchlessinger P) (-2)) :=
  inferInstance

end Algebra.Presentation.LichtenbaumSchlessinger
