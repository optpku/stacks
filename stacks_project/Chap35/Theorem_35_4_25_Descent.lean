/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.UniversallyInjective.ModuleProperties

/-!
# Compatibility checks for module properties under universally injective base change

The reusable declarations are provided by
`ReasLib.LinearAlgebra.UniversallyInjective.ModuleProperties`.
-/

open scoped TensorProduct

universe u v w

#check (Module.Finite.iff_tensorProduct_of_universallyInjective :
  ∀ {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M],
    LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S) →
      (Module.Finite R M ↔ Module.Finite S (S ⊗[R] M)))

#check (Module.FinitePresentation.iff_tensorProduct_of_universallyInjective :
  ∀ {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M],
    LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S) →
      (Module.FinitePresentation R M ↔ Module.FinitePresentation S (S ⊗[R] M)))

#check (Module.Flat.iff_tensorProduct_of_universallyInjective :
  ∀ {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M],
    LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S) →
      (Module.Flat R M ↔ Module.Flat S (S ⊗[R] M)))

#check (Module.FaithfullyFlat.iff_tensorProduct_of_universallyInjective :
  ∀ {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M],
    LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S) →
      (Module.FaithfullyFlat R M ↔ Module.FaithfullyFlat S (S ⊗[R] M)))

#check (Module.FiniteProjective.iff_tensorProduct_of_universallyInjective :
  ∀ {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M],
    LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S) →
      (Module.FiniteProjective R M ↔ Module.FiniteProjective S (S ⊗[R] M)))
