/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ClassGroup
public import ReasLib.AlgebraicGeometry.Scheme.Module.RankOneReflexive.Tensor

/-!
# Rank-one reflexive modules and the Weil divisor class group

This file compares the group of isomorphism classes of rank-one coherent reflexive modules on a
normal scheme with its Weil divisor class group.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- On an integral locally Noetherian normal scheme, the additive group of isomorphism classes of
rank-one coherent reflexive modules is isomorphic to the Weil divisor class group. -/
theorem rankOneReflexiveClassGroup_addEquiv_weilDivisorClassGroup
    (hXnormal : X.isNormal) :
    Nonempty (rankOneReflexiveClassGroup hXnormal ≃+ Cl(X)) := sorry

end AlgebraicGeometry.Scheme.Modules
