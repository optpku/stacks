/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import ReasLib.LinearAlgebra.UniversallyInjective.ModuleProperties

/-!
# Algebra properties under universally injective base change

This module records preservation and reflection of five standard algebra properties along a
universally injective map of commutative rings.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A]

namespace Algebra.FiniteType

/-- Finite type is preserved and reflected by universally injective base change. -/
theorem iff_tensorProduct_of_universallyInjective
    (hRS : LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S)) :
    Algebra.FiniteType R A ↔ Algebra.FiniteType S (S ⊗[R] A) := sorry

end Algebra.FiniteType

namespace Algebra.FinitePresentation

/-- Finite presentation is preserved and reflected by universally injective base change. -/
theorem iff_tensorProduct_of_universallyInjective
    (hRS : LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S)) :
    Algebra.FinitePresentation R A ↔ Algebra.FinitePresentation S (S ⊗[R] A) := sorry

end Algebra.FinitePresentation

namespace Algebra.FormallyUnramified

/-- Formal unramifiedness is preserved and reflected by universally injective base change. -/
theorem iff_tensorProduct_of_universallyInjective
    (hRS : LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S)) :
    Algebra.FormallyUnramified R A ↔ Algebra.FormallyUnramified S (S ⊗[R] A) := sorry

end Algebra.FormallyUnramified

namespace Algebra.Unramified

/-- Unramifiedness is preserved and reflected by universally injective base change. -/
theorem iff_tensorProduct_of_universallyInjective
    (hRS : LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S)) :
    Algebra.Unramified R A ↔ Algebra.Unramified S (S ⊗[R] A) := sorry

end Algebra.Unramified

namespace Algebra.Etale

/-- Étaleness is preserved and reflected by universally injective base change. -/
theorem iff_tensorProduct_of_universallyInjective
    (hRS : LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S)) :
    Algebra.Etale R A ↔ Algebra.Etale S (S ⊗[R] A) := sorry

end Algebra.Etale
