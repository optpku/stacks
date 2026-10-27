/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import ReasLib.CategoryTheory.Adjunction.Abelian
public import ReasLib.CategoryTheory.Monoidal.Closed.Dualizable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dualizable tensor factors and injective objects

An object with duals on both sides gives a tensor functor whose opposite tensor factor is an
exact left adjoint.  Consequently tensoring by the original object preserves injectives.  The
explicit-pairing API is independent of a braiding; the object-property and closed-monoidal
interfaces provide the canonical specializations used in geometry.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [MonoidalPreadditive C]

namespace ExactPairing

/-- Tensoring on the left by the first object of a two-sided exact pairing preserves
injective objects. -/
@[stacks 01E7 "two-sided categorical core"]
theorem tensorLeft_preservesInjectiveObjects_of_reverse
    {X Y : C} (p : ExactPairing X Y) (q : ExactPairing Y X) :
    (tensorLeft X).PreservesInjectiveObjects := by
  letI : PreservesLimits (tensorLeft Y) :=
    q.tensorLeftAdjunction.rightAdjoint_preservesLimits
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    p.tensorLeftAdjunction

/-- Tensoring on the right by the first object of a two-sided exact pairing preserves
injective objects. -/
@[stacks 01E7 "two-sided categorical core, opposite tensor order"]
theorem tensorRight_preservesInjectiveObjects_of_reverse
    {X Y : C} (p : ExactPairing X Y) (q : ExactPairing Y X) :
    (tensorRight X).PreservesInjectiveObjects := by
  letI : PreservesLimits (tensorRight Y) :=
    p.tensorRightAdjunction.rightAdjoint_preservesLimits
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    q.tensorRightAdjunction

end ExactPairing

section Braided

variable [BraidedCategory C]

namespace ExactPairing

/-- Left tensoring by the first object of an exact pairing preserves injectives in a braided
monoidal abelian category. -/
theorem tensorLeft_preservesInjectiveObjects
    {X Y : C} (p : ExactPairing X Y) :
    (tensorLeft X).PreservesInjectiveObjects :=
  p.tensorLeft_preservesInjectiveObjects_of_reverse p.braidedSwap

/-- Right tensoring by the first object of an exact pairing preserves injectives in a braided
monoidal abelian category. -/
theorem tensorRight_preservesInjectiveObjects
    {X Y : C} (p : ExactPairing X Y) :
    (tensorRight X).PreservesInjectiveObjects :=
  p.tensorRight_preservesInjectiveObjects_of_reverse p.braidedSwap

end ExactPairing

namespace IsRightDualizable

/-- Left tensoring by a dualizable object in a braided monoidal abelian category preserves
injective objects. -/
theorem tensorLeft_preservesInjectiveObjects
    {X : C} (hX : IsRightDualizable X) :
    (tensorLeft X).PreservesInjectiveObjects := by
  obtain ⟨hX⟩ := hX
  exact hX.exact.tensorLeft_preservesInjectiveObjects

/-- Right tensoring by a dualizable object in a braided monoidal abelian category preserves
injective objects. -/
theorem tensorRight_preservesInjectiveObjects
    {X : C} (hX : IsRightDualizable X) :
    (tensorRight X).PreservesInjectiveObjects := by
  obtain ⟨hX⟩ := hX
  exact hX.exact.tensorRight_preservesInjectiveObjects

/-- Tensoring a dualizable object on the left with an injective object gives an injective
object. -/
theorem tensor_injective
    {X I : C} (hX : IsRightDualizable X) (hI : Injective I) :
    Injective (X ⊗ I) := by
  letI := hX.tensorLeft_preservesInjectiveObjects
  exact (tensorLeft X).injective_obj_of_injective hI

/-- Tensoring an injective object on the left with a dualizable object gives an injective
object. -/
theorem injective_tensor
    {X I : C} (hX : IsRightDualizable X) (hI : Injective I) :
    Injective (I ⊗ X) := by
  letI := hX.tensorRight_preservesInjectiveObjects
  exact (tensorRight X).injective_obj_of_injective hI

end IsRightDualizable

section Closed

variable [MonoidalClosed C]

namespace MonoidalClosed.Dual

/-- The canonical closed dual makes left tensoring by a dualizable object preserve
injectives. -/
instance tensorLeft_preservesInjectiveObjects
    (X : C) [IsIso (tensorIhomUnitToEnd X)] :
    (tensorLeft X).PreservesInjectiveObjects :=
  (exactPairing X).tensorLeft_preservesInjectiveObjects

/-- The canonical closed dual makes right tensoring by a dualizable object preserve
injectives. -/
instance tensorRight_preservesInjectiveObjects
    (X : C) [IsIso (tensorIhomUnitToEnd X)] :
    (tensorRight X).PreservesInjectiveObjects :=
  (exactPairing X).tensorRight_preservesInjectiveObjects

end MonoidalClosed.Dual

end Closed

end Braided

end CategoryTheory
