/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.ConstantAdicCompletion

/-!
# Lemma 61.28.3

A sheaf of modules on the small pro-étale site of a weakly contractible
affine scheme, complete with constant finite-type reductions, is a completed
constant sheaf of a finite module over the adic completion.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Opposite

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

/- Lemma 61.28.3 -/
@[stacks 09BV] #check
  (AlgebraicGeometry.Scheme.ProEt.exists_iso_constantAdicCompletion :
    {X : Scheme.{u}} → [IsAffine X] →
      [(ProEt.topology X).IsWeaklyContractible (ProEt.mk (𝟙 X))] →
      {Λ : Type w} → [CommRing Λ] → [IsNoetherianRing Λ] →
      [HasWeakSheafify (ProEt.topology X) (ModuleCat.{w} Λ)] →
      [HasWeakSheafify (ProEt.topology X) RingCat.{w}] →
      [(ProEt.topology X).WEqualsLocallyBijective RingCat.{w}] →
      [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{w}] →
      [(ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{w}] →
      [∀ U : X.ProEt, HasWeakSheafify ((ProEt.topology X).over U) AddCommGrpCat.{w}] →
      [∀ U : X.ProEt, ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{w}] →
      (I : Ideal Λ) → (F : Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) →
      IsIso (Sheaf.IdealPower.toLimit I F) →
      (∀ n : ℕ,
        Sheaf.IsConstant (ProEt.topology X) (Sheaf.IdealPower.quotient I F n.succ)) →
      ((Sheaf.IdealPower.quotient I F 1).toConstantModuleSheaf).IsFiniteType →
      ∃ M : ModuleCat.{w} (AdicCompletion I Λ),
        Module.Finite (AdicCompletion I Λ) M ∧
          Nonempty (F ≅ ConstantSheaf.AdicCompletion.ofAdicModule (ProEt.topology X) I M))

end AlgebraicGeometry.Scheme
