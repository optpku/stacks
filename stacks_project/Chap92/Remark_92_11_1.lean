/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_5_3
public import stacks_project.Chap92.Lemma_92_5_7
public import stacks_project.Chap92.Remark_92_11_1_Ideal
public import stacks_project.Chap92.«92_11_1_1»
public import stacks_project.Chap92.«92_11_1_2»
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

/-!
# Kernel vanishing and naive cotangent comparisons on `C_{B/A}`

Remark 92.11.1 records that `Lπ!(𝒥) = 0` for `𝒥 = Ker(O ⟶ underline{B})`, that
`H_0` and `H_1` of `𝒥/𝒥²` vanish, and the resulting comparison maps from a
polynomial arrow into `L_{B/A}` and `τ_{≥ -1} L_{B/A}`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra
open Algebra.PolynomialSite
open Algebra.CotangentComplex
open Algebra.NaiveCotangent
open CommAlgCat.Over.Polynomial
open CommRingCat.Under.CotangentComplex
open Site
open scoped CategoryTheory

noncomputable section

universe u q q'

namespace Algebra.PolynomialSite

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

section AbelianGroups

variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q'} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/-- Remark 92.11.1 (1). Let `A → B` be a ring map. Working on `C_{B/A}` as in
Section 92.4, let `𝒥 ⊂ O` be the kernel of `O ⟶ underline{B}`. Then
`Lπ!(𝒥) = 0`. -/
@[stacks 08R7]
theorem lowerShriek_kernel_isZero :
    IsZero
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (kernelPresheaf A B))) :=
  sorry

end AbelianGroups

section Modules

variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

/-- Remark 92.11.1 (2). With `𝒥` the kernel of `O ⟶ underline{B}` on `C_{B/A}`,
`Tor_0^O(𝒥, underline{B}) = 𝒥/𝒥²` and `Lπ!(𝒥 ⊗_O^L underline{B}) = 0` imply
`H_0(C_{B/A}, 𝒥/𝒥²) = 0`. -/
@[stacks 08R7]
theorem conormal_homology_zero_isZero :
    IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (0 : ℤ)).obj
        (((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)) ⋙
          Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
          (conormalSheaf A B))) :=
  sorry

/-- Remark 92.11.1 (3). With `𝒥` the kernel of `O ⟶ underline{B}` on `C_{B/A}`,
the same vanishing of `Lπ!(𝒥 ⊗_O^L underline{B})` implies
`H_1(C_{B/A}, 𝒥/𝒥²) = 0`. -/
@[stacks 08R7]
theorem conormal_homology_negOne_isZero :
    IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-1 : ℤ)).obj
        (((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)) ⋙
          Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
          (conormalSheaf A B))) :=
  sorry

end Modules

end Algebra.PolynomialSite

/- The identification `Lπ!(𝒥 ⟶ Ω) = L_{B/A}` on the standard resolution. -/
@[stacks 08R7] #check omegaInr_quasiIso

/- The comparison map 92.11.1.1: `(J ⟶ Ω_{P/A} ⊗_P B) ⟶ L_{B/A}` in `D(A)`. -/
@[stacks 08R7] #check comparisonDerived

/- The truncated identification `τ_{≥ -1} Lπ!(𝒥/𝒥² ⟶ Ω) = τ_{≥ -1} L_{B/A}`. -/
@[stacks 08R7] #check truncGEEvaluationIso

/- The comparison map 92.11.1.2: `(J/J² ⟶ Ω_{P/A} ⊗_P B) ⟶ τ_{≥ -1} L_{B/A}` in `D(B)`. -/
@[stacks 08R7] #check naiveCotangentToTruncGE

/- Recalled identification `L_{B/A} = Lπ!(Ω)`. -/
#check lowerShriek_omega
