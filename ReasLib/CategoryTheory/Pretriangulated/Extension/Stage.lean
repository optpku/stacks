/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosureShift
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.FiniteCoproductClosure
public import ReasLib.CategoryTheory.Pretriangulated.Extension.Coproduct

@[expose] public section

/-!
# Additive Extension Stages

This leaf packages finite iterated extensions of the additive closure of an
object property.  The natural-number-indexed construction is the primary
owner; the positive-indexed stage is the source-facing reindexing.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.ObjectProperty

section

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]

/-- Additive closure preserves stability under integer shifts. -/
@[stacks 0FX4]
instance additiveClosure_isStableUnderShift (P : ObjectProperty C)
    [P.IsStableUnderShift ℤ] :
    P.additiveClosure.IsStableUnderShift ℤ := sorry

end

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The `n`-fold additive extension stage, where `n` counts extension operations. -/
@[stacks 0FX4]
abbrev additiveExtensionStageNat (P : ObjectProperty C) (n : ℕ) : ObjectProperty C :=
  (P.additiveClosure.extensionProductIter n).retractClosure

/-- The positive source-facing additive extension stage, indexed so that stage `1` has no
extension operation. -/
@[stacks 0FX4]
abbrev additiveExtensionStage (P : ObjectProperty C) (n : ℕ+) : ObjectProperty C :=
  additiveExtensionStageNat P n.natPred

/-- The first positive additive extension stage is the retract closure of the additive closure. -/
@[stacks 0FX4]
theorem additiveExtensionStage_one (P : ObjectProperty C) :
    additiveExtensionStage P 1 = P.additiveClosure.retractClosure := sorry

/-- Additive extension stages are monotone in their generating object property. -/
theorem additiveExtensionStageNat_monotone {P Q : ObjectProperty C} (hPQ : P ≤ Q) (n : ℕ) :
    additiveExtensionStageNat P n ≤ additiveExtensionStageNat Q n := sorry

/-- Positive additive extension stages are monotone in their generating object property. -/
@[stacks 0FX4]
theorem additiveExtensionStage_monotone {P Q : ObjectProperty C} (hPQ : P ≤ Q) (n : ℕ+) :
    additiveExtensionStage P n ≤ additiveExtensionStage Q n := sorry

/-- Shift stability passes to natural-number-indexed additive extension stages. -/
instance additiveExtensionStageNat_isStableUnderShift (P : ObjectProperty C)
    [P.IsStableUnderShift ℤ] (n : ℕ) :
    (additiveExtensionStageNat P n).IsStableUnderShift ℤ := sorry

/-- Shift stability passes to positive additive extension stages. -/
@[stacks 0FX4]
instance additiveExtensionStage_isStableUnderShift (P : ObjectProperty C)
    [P.IsStableUnderShift ℤ] (n : ℕ+) :
    (additiveExtensionStage P n).IsStableUnderShift ℤ := sorry

/-- Natural-number-indexed additive extension stages are closed under binary coproducts. -/
instance additiveExtensionStageNat_isClosedUnderBinaryCoproducts
    (P : ObjectProperty C) (n : ℕ) :
    (additiveExtensionStageNat P n).IsClosedUnderBinaryCoproducts := sorry

/-- Positive additive extension stages are closed under binary coproducts. -/
@[stacks 0FX4]
instance additiveExtensionStage_isClosedUnderBinaryCoproducts
    (P : ObjectProperty C) (n : ℕ+) :
    (additiveExtensionStage P n).IsClosedUnderBinaryCoproducts := sorry

/-- An object of `P` belongs to the retract closure of the additive closure of `P`. -/
theorem mem_additiveClosure_retractClosure_of_mem (P : ObjectProperty C) {X : C} (hX : P X) :
    P.additiveClosure.retractClosure X := sorry

/-- Every natural-number-indexed additive extension stage lies in any retract-stable,
finite-coproduct-closed property that is closed under middle terms of distinguished triangles. -/
theorem additiveExtensionStageNat_le_of_le {P Q : ObjectProperty C}
    [Q.IsStableUnderRetracts] [Q.IsClosedUnderFiniteCoproducts]
    [Q.IsTriangulatedClosed₂] (hPQ : P ≤ Q) (n : ℕ) :
    additiveExtensionStageNat P n ≤ Q := sorry

/-- Every positive additive extension stage lies in any retract-stable,
finite-coproduct-closed property that is closed under middle terms of distinguished triangles. -/
@[stacks 0FX4]
theorem additiveExtensionStage_le_of_le {P Q : ObjectProperty C}
    [Q.IsStableUnderRetracts] [Q.IsClosedUnderFiniteCoproducts]
    [Q.IsTriangulatedClosed₂] (hPQ : P ≤ Q) (n : ℕ+) :
    additiveExtensionStage P n ≤ Q := sorry

end

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- Composing a natural-number-indexed stage with one further block of extensions is the retract
closure of the extension product of the two stages. -/
@[stacks 0FX4]
theorem additiveExtensionStageNat_succ_add (P : ObjectProperty C) (n m : ℕ) :
    additiveExtensionStageNat P (n.succ + m) =
      (extensionProduct (additiveExtensionStageNat P n)
        (additiveExtensionStageNat P m)).retractClosure := sorry

/-- Addition of positive additive extension stages is the retract closure of the extension
product of the two stages. -/
@[stacks 0FX4]
theorem additiveExtensionStage_add (P : ObjectProperty C) (n m : ℕ+) :
    additiveExtensionStage P (n + m) =
      (extensionProduct (additiveExtensionStage P n) (additiveExtensionStage P m)).retractClosure := sorry

end

end CategoryTheory.ObjectProperty
