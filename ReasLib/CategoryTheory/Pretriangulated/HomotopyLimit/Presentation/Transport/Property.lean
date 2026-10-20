/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Transport.Object
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Transport.Tower
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism-Closed Homotopy-Limit Properties

This leaf exposes both currying directions of `HomotopyLimit.IsOf` through the standard
`ObjectProperty.IsClosedUnderIsomorphisms` interface.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.HomotopyLimit.IsOf

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Sequential inverse systems for which `X` is a homotopy limit, regarded as an object
property of the inverse-system category. -/
@[stacks 08TC]
def inverseSystem (X : D) : ObjectProperty (SequentialInverseSystem D) :=
  fun K => HomotopyLimit.IsOf K X

/-- Membership in `IsOf.inverseSystem X` is the homotopy-limit relation with target `X`. -/
@[simp]
theorem inverseSystem_apply (X : D) (K : SequentialInverseSystem D) :
    inverseSystem X K ↔ HomotopyLimit.IsOf K X := sorry

/-- Homotopy-limit objects of a fixed sequential inverse system are closed under
isomorphisms. -/
@[stacks 08TC]
instance isClosedUnderIsomorphisms (K : SequentialInverseSystem D) :
    ObjectProperty.IsClosedUnderIsomorphisms (HomotopyLimit.IsOf K) := sorry

/-- Sequential inverse systems presenting a fixed homotopy-limit object are closed under
isomorphisms. -/
@[stacks 08TC]
instance inverseSystemIsClosedUnderIsomorphisms (X : D) :
    ObjectProperty.IsClosedUnderIsomorphisms (inverseSystem X) := sorry

end CategoryTheory.HomotopyLimit.IsOf
