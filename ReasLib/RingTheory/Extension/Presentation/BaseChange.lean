/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Base change of algebra presentations

This leaf records the kernel and evaluation interfaces of presentation base
change independently of any selected relation or Jacobian data.
-/

@[expose] public section

open scoped TensorProduct

universe u v w t x

namespace Algebra.Presentation.BaseChange

variable {R : Type u} {A : Type v} {R' : Type w}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']
variable {ι : Type t} {σ : Type x}

/-- The kernel of a presentation after coefficient base change is the
extension of its original kernel. -/
theorem ker (P : Presentation R A ι σ) :
    (P.baseChange R').ker =
      Ideal.map (MvPolynomial.map (algebraMap R R')) P.ker := sorry

/-- Evaluating a coefficientwise-mapped presentation polynomial after base
change gives its pure tensor evaluation. -/
theorem algebraMap_map (P : Presentation R A ι σ) (p : P.Ring) :
    algebraMap (P.baseChange R').Ring (R' ⊗[R] A)
        (MvPolynomial.map (algebraMap R R') p) =
      (1 : R') ⊗ₜ[R] algebraMap P.Ring A p := sorry

end Algebra.Presentation.BaseChange
