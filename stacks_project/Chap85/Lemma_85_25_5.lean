/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Simplicial.ProperDescent.Equivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.SimplicialObject Opposite
open scoped Simplicial

noncomputable section

universe u

namespace LCCat

variable {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
variable (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)
variable [HasSheafify (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}]
variable [HasSheafify (zariskiTopology (constSpace X.obj)) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}]
variable [∀ n : ℕ, HasSheafify
    (Opens.grothendieckTopology ((forgetToTop.obj U).obj (op ⦋n⦌))) AddCommGrpCat.{u}]
variable [(augmentationPushforward (toTopCatAugmentation a)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}))]

variable (ha : IsProperHypercovering a)

/- Lemma 85.25.5. A proper hypercovering induces bounded-below derived descent
with canonical inverse image and derived direct image as quasi-inverse. -/
@[stacks 0DAH] #check (LCCat.plusCartesianEquivalence a ha :
  DerivedCategory.Plus
    (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}) ≌
    DerivedCategory.Plus.CohomologyIn
      (cartesianProperty (forgetToTop.obj U) AddCommGrpCat.{u}))

#check (LCCat.plusCartesianEquivalence_functor a ha :
  (LCCat.plusCartesianEquivalence a ha).functor =
    plusInverseImageCartesian (toTopCatAugmentation a))

#check (LCCat.plusCartesianEquivalence_inverse a ha :
  (LCCat.plusCartesianEquivalence a ha).inverse =
    plusDirectImageCartesian (toTopCatAugmentation a))

end LCCat

end
