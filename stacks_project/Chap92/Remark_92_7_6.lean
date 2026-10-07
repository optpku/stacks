module

public import stacks_project.Chap92.Remark_92_7_6_Comparison
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

/-!
# Canonical identification of `Ω_{Q̄_•/B} ⊗ C` with `Ω_{R_•/B} ⊗ C`

Remark 92.7.6 explains the comparison maps `Q̄_• → R̄_•` and `R_• → R̄_•` induced by
the functoriality square of standard resolutions, and records that the resulting
maps on naive differentials are quasi-isomorphisms whose derived-category composite
identifies `Ω_{Q̄_•/B} ⊗_{Q̄_•} C` with `Ω_{R_•/B} ⊗_{R_•} C`.
-/

@[expose] public section

open CategoryTheory
open Algebra
open Algebra.PolynomialSite
open Algebra.CotangentComplex

noncomputable section

universe u q

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- Remark 92.7.6 (1): if `B → C` is injective, then each term `R_n` of the standard
resolution of `C` over `B` is a polynomial algebra over the corresponding term `S_n` of
the standard resolution of `B` over `B`. -/
@[stacks 08SE]
theorem isPolynomial_standardR_over_standardS_of_injective (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    IsPolynomial (standardS B n) (standardR B C n) :=
  sorry

/-- Remark 92.7.6 (2): `R̄_• = R_• ⊗_{S_•} B` is a simplicial polynomial resolution of
`C` over `B`. -/
@[stacks 08SE]
theorem isResolution_barR (h_inj : Function.Injective (algebraMap B C)) :
    IsResolution (barRHom B C h_inj) :=
  sorry

/- Remark 92.7.6 (3): the commutative square of standard resolutions induces a canonical
map `Q̄_• = Q_• ⊗_{P_•} B ⟶ R̄_•`. -/
@[stacks 08SE] #check barQToBarR

/- Remark 92.7.6 (4): the induced map
`Ω_{R_•/B} ⊗_{R_•} C ⟶ Ω_{R̄_•/B} ⊗_{R̄_•} C` is a quasi-isomorphism. -/
@[stacks 08SE] #check omegaEvalToBarR_quasiIso

/- Remark 92.7.6 (5): the induced map
`Ω_{Q̄_•/B} ⊗_{Q̄_•} C ⟶ Ω_{R̄_•/B} ⊗_{R̄_•} C` is a quasi-isomorphism. -/
@[stacks 08SE] #check omegaBarQToBarR_quasiIso

/-- Remark 92.7.6 (6): composing one of these quasi-isomorphisms with the inverse of the
other identifies `Ω_{Q̄_•/B} ⊗_{Q̄_•} C` with `Ω_{R_•/B} ⊗_{R_•} C` in `D(C)`. -/
@[stacks 08SE]
theorem barQ_iso_omegaEval_of_injective (h_inj : Function.Injective (algebraMap B C))
    [HasDerivedCategory.{q} (ModuleCat.{u} C)] :
    IsIso (DerivedCategory.Q.map (omegaBarQToBarR A B C h_inj) ≫
      inv (DerivedCategory.Q.map (omegaEvalToBarR B C h_inj))) :=
  sorry
