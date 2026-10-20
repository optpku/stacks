/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import ReasLib.LinearAlgebra.UniversallyInjective
public import ReasLib.RingTheory.Finiteness.Projective

/-!
# Module properties under universally injective base change

This module records preservation and reflection of standard module properties along a
universally injective algebra map.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

namespace Module.Finite

/-- Finite generation is preserved and reflected by universally injective scalar extension. -/
theorem iff_tensorProduct_of_universallyInjective
    (hRS : LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S)) :
    Module.Finite R M ↔ Module.Finite S (S ⊗[R] M) := sorry

end Module.Finite

namespace Module.FinitePresentation

/-- Finite presentation is preserved and reflected by universally injective scalar extension. -/
theorem iff_tensorProduct_of_universallyInjective
    (hRS : LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S)) :
    Module.FinitePresentation R M ↔ Module.FinitePresentation S (S ⊗[R] M) := sorry

end Module.FinitePresentation

namespace Module.Flat

/-- Flatness is preserved and reflected by universally injective scalar extension. -/
theorem iff_tensorProduct_of_universallyInjective
    (hRS : LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S)) :
    Module.Flat R M ↔ Module.Flat S (S ⊗[R] M) := sorry

end Module.Flat

namespace Module.FaithfullyFlat

/-- Faithful flatness is preserved and reflected by universally injective scalar extension. -/
theorem iff_tensorProduct_of_universallyInjective
    (hRS : LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S)) :
    Module.FaithfullyFlat R M ↔ Module.FaithfullyFlat S (S ⊗[R] M) := sorry

end Module.FaithfullyFlat

namespace Module.FiniteProjective

/-- Finite projectivity is preserved and reflected by universally injective scalar extension. -/
theorem iff_tensorProduct_of_universallyInjective
    (hRS : LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S)) :
    Module.FiniteProjective R M ↔ Module.FiniteProjective S (S ⊗[R] M) := sorry

end Module.FiniteProjective
