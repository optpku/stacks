/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.UniversallyInjective.ModuleProperties
import StacksCheckRecall

open scoped TensorProduct

universe u v w

/- Theorem 35.4.25 (1): finite generation is preserved and reflected by universally injective
scalar extension. -/
@[stacks 08XD] #check (Module.Finite.iff_tensorProduct_of_universallyInjective :
  ∀ {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M],
    LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S) →
      (Module.Finite R M ↔ Module.Finite S (S ⊗[R] M)))

/- Theorem 35.4.25 (2): finite presentation is preserved and reflected by universally injective
scalar extension. -/
@[stacks 08XD] #check (Module.FinitePresentation.iff_tensorProduct_of_universallyInjective :
  ∀ {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M],
    LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S) →
      (Module.FinitePresentation R M ↔ Module.FinitePresentation S (S ⊗[R] M)))

/- Theorem 35.4.25 (3): flatness is preserved and reflected by universally injective scalar
extension. -/
@[stacks 08XD] #check (Module.Flat.iff_tensorProduct_of_universallyInjective :
  ∀ {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M],
    LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S) →
      (Module.Flat R M ↔ Module.Flat S (S ⊗[R] M)))

/- Theorem 35.4.25 (4): faithful flatness is preserved and reflected by universally injective
scalar extension. -/
@[stacks 08XD] #check (Module.FaithfullyFlat.iff_tensorProduct_of_universallyInjective :
  ∀ {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M],
    LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S) →
      (Module.FaithfullyFlat R M ↔ Module.FaithfullyFlat S (S ⊗[R] M)))

/- Theorem 35.4.25 (5): finite projectivity is preserved and reflected by universally injective
scalar extension. -/
@[stacks 08XD] #check (Module.FiniteProjective.iff_tensorProduct_of_universallyInjective :
  ∀ {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M],
    LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S) →
      (Module.FiniteProjective R M ↔ Module.FiniteProjective S (S ⊗[R] M)))
