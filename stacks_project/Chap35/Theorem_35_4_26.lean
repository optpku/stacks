/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Algebra.UniversallyInjective
import StacksCheckRecall

open scoped TensorProduct

universe u v w

/- Theorem 35.4.26 (1): finite type is preserved and reflected by universally injective base
change. -/
@[stacks 08XE] #check (Algebra.FiniteType.iff_tensorProduct_of_universallyInjective :
  ∀ {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A],
    LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S) →
      (Algebra.FiniteType R A ↔ Algebra.FiniteType S (S ⊗[R] A)))

/- Theorem 35.4.26 (2): finite presentation is preserved and reflected by universally injective
base change. -/
@[stacks 08XE] #check (Algebra.FinitePresentation.iff_tensorProduct_of_universallyInjective :
  ∀ {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A],
    LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S) →
      (Algebra.FinitePresentation R A ↔ Algebra.FinitePresentation S (S ⊗[R] A)))

/- Theorem 35.4.26 (3): formal unramifiedness is preserved and reflected by universally injective
base change. -/
@[stacks 08XE] #check (Algebra.FormallyUnramified.iff_tensorProduct_of_universallyInjective :
  ∀ {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A],
    LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S) →
      (Algebra.FormallyUnramified R A ↔ Algebra.FormallyUnramified S (S ⊗[R] A)))

/- Theorem 35.4.26 (4): unramifiedness is preserved and reflected by universally injective base
change. -/
@[stacks 08XE] #check (Algebra.Unramified.iff_tensorProduct_of_universallyInjective :
  ∀ {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A],
    LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S) →
      (Algebra.Unramified R A ↔ Algebra.Unramified S (S ⊗[R] A)))

/- Theorem 35.4.26 (5): étaleness is preserved and reflected by universally injective base
change. -/
@[stacks 08XE] #check (Algebra.Etale.iff_tensorProduct_of_universallyInjective :
  ∀ {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A],
    LinearMap.UniversallyInjective.{u, u, v, max u v w} (Algebra.linearMap R S) →
      (Algebra.Etale R A ↔ Algebra.Etale S (S ⊗[R] A)))
