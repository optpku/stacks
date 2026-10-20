/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.DescentDatum.Reconstruction

/-!
# Base change of effective module descent data

This file relates effectiveness of module descent data to faithfully flat base change.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Module.DescentDatum

universe u

variable {R A R' : Type u}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']
variable [Module.FaithfullyFlat R A] [Module.FaithfullyFlat R R']

/-- If every module descent datum for the base change `R' → R' ⊗[R] A` is
effective, then every module descent datum for `R → A` is effective. -/
theorem allEffective_of_baseChange
    (h_effective : ∀ (N' : Type u) [AddCommGroup N'] [Module R' N']
      [Module (R' ⊗[R] A) N'] [IsScalarTower R' (R' ⊗[R] A) N']
      [SMulCommClass R' (R' ⊗[R] A) N']
      (D' : DescentDatum R' (R' ⊗[R] A) N'), D'.IsEffective) :
    ∀ (N : Type u) [AddCommGroup N] [Module R N] [Module A N]
      [IsScalarTower R A N] [SMulCommClass R A N]
      (D : DescentDatum R A N), D.IsEffective := sorry

end Module.DescentDatum
