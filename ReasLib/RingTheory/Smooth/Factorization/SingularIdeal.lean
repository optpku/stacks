/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.AlgHom.Factorisation
public import ReasLib.RingTheory.Smooth.SingularLocus

@[expose] public section

/-!
# Smooth factorizations from singular-ideal control

This leaf contains the global singular-ideal criterion for the existence of a
smooth factorization.
-/

universe u v w

namespace AlgHom.Factorisation.Smooth

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ] [Algebra.FinitePresentation R A]

/-- If the image of the singular ideal is the unit ideal, an algebra map
factors through a smooth algebra. -/
@[stacks 07EU]
theorem nonempty_of_map_singularIdeal_eq_top
    (φ : A →ₐ[R] Λ)
    (hHtop : Ideal.map φ (Algebra.singularIdeal R A) = ⊤) :
    Nonempty (AlgHom.Factorisation.Smooth φ) := sorry

end AlgHom.Factorisation.Smooth
