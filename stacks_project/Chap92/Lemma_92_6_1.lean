/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_6_1_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived lower shriek after inverse image along a derived-tensor quasi-isomorphism

Lemma 92.6.1 records that if a commutative square of rings induces a quasi-isomorphism
`B ⊗[A]^L A' = B'`, then with the notation of (92.6.0.2) one has
`Lπ_!(g⁻¹ F') = Lπ'_!(F')` in `D(Ab)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open RingedSite.Cotangent
open RingedSite.Cotangent.Functoriality
open scoped CategoryTheory

noncomputable section

universe u q q' t

variable {A A' B B' : CommRingCat.{u}}
variable {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}
variable [HasColimitsOfShape (polynomialSite α)ᵒᵖ AddCommGrpCat.{u}]
variable [HasColimitsOfShape (polynomialSite β)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{t} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((polynomialSite α)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [HasDerivedCategory.{q'} ((polynomialSite β)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (polynomialSite α) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((polynomialSite α)ᵒᵖ ⥤ AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (polynomialSite β) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((polynomialSite β)ᵒᵖ ⥤ AddCommGrpCat.{u}) (up ℤ))]

/-- Lemma 92.6.1. Assume (92.6.0.1) induces a quasi-isomorphism `B ⊗[A]^L A' = B'`.
Then, with notation as in (92.6.0.2) and `F'` in `Ab(C')`, one has
`Lπ_!(g⁻¹ F') = Lπ'_!(F')` in `D(Ab)`. Here `g⁻¹` is
`presheafInverseImage (mapOp sq)`, `π` is `Lπ![polynomialSite α, AddCommGrpCat]`,
and `π'` is `Lπ![polynomialSite β, AddCommGrpCat]`. -/
@[stacks 08QP]
theorem inverseImage_lowerShriek (sq : CommSq ρ α β φ)
    (h : InducesDerivedTensorQuasiIso sq) :
    IsIsomorphic
      ((DerivedCategory.singleFunctor
          ((polynomialSite β)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        (Functor.presheafInverseImage (mapOp sq) AddCommGrpCat.{u}).mapDerivedCategory ⋙
        Lπ![(polynomialSite α), AddCommGrpCat.{u}])
      ((DerivedCategory.singleFunctor
          ((polynomialSite β)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(polynomialSite β), AddCommGrpCat.{u}]) :=
  sorry
