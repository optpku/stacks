/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Algebra structures on a closed fiber

For a local ring `A` and an `A`-algebra `B`, the canonical closed fiber
`Ideal.Fiber (IsLocalRing.maximalIdeal A) B` is an algebra over both the ordinary residue field
of `A` and the target ring `B`.  These named instances keep that pair of structures stable for
regularity and formal-smoothness statements.

@stack 0H7U
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u v

namespace IsLocalRing.ResidueField

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]

/-- The ordinary residue field of a local ring acts canonically on its closed fiber.  Internally,
the action is transported through `maximalIdealAlgEquiv A` from the maximal ideal's residue-field
presentation. -/
@[stacks 0H7U "ordinary residue-field algebra on the closed fiber"]
noncomputable instance instAlgebraClosedFiber :
    Algebra (ResidueField A) (Ideal.Fiber (maximalIdeal A) B) :=
  let _ : Algebra (maximalIdeal A).ResidueField (Ideal.Fiber (maximalIdeal A) B) :=
    Algebra.TensorProduct.leftAlgebra
  ((algebraMap (maximalIdeal A).ResidueField (Ideal.Fiber (maximalIdeal A) B)).comp
    (maximalIdealAlgEquiv A).toRingEquiv.toRingHom).toAlgebra

/-- The target ring acts canonically on its closed fiber through the right tensor factor. -/
@[stacks 0H7U "target-ring algebra on the closed fiber"]
noncomputable instance instTargetAlgebraClosedFiber :
    Algebra B (Ideal.Fiber (maximalIdeal A) B) :=
  Algebra.TensorProduct.rightAlgebra

end IsLocalRing.ResidueField
