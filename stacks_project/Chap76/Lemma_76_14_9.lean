/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap76.Lemma_76_14_8

/-!
# Closed immersions of algebraic spaces

A morphism of algebraic spaces is a closed immersion if and only if it is
universally closed and unramified together with either a monomorphism or
universal injectivity, and if and only if it is universally closed and locally
of finite type together with either a monomorphism or the formally unramified
universally injective package.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.14.9: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is a closed
immersion; `f` is universally closed, unramified, and a monomorphism; `f` is
universally closed, unramified, and universally injective; `f` is universally
closed, locally of finite type, and a monomorphism; `f` is universally closed,
universally injective, locally of finite type, and formally unramified. -/
@[stacks 05W8]
theorem tfae_isClosedImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    List.TFAE [
      IsClosedImmersion f,
      UniversallyClosed f ∧ Unramified f ∧ Mono f,
      UniversallyClosed f ∧ Unramified f ∧ UniversallyInjective f,
      UniversallyClosed f ∧ LocallyOfFiniteType f ∧ Mono f,
      UniversallyClosed f ∧ UniversallyInjective f ∧ LocallyOfFiniteType f ∧
        FormallyUnramified f] :=
  sorry

namespace IsClosedImmersion

/-- A morphism of algebraic spaces is a closed immersion if and only if it is
universally closed, unramified, and a monomorphism. -/
theorem iff_universallyClosed_unramified_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsClosedImmersion f ↔ UniversallyClosed f ∧ Unramified f ∧ Mono f :=
  sorry

/-- A morphism of algebraic spaces is a closed immersion if and only if it is
universally closed, unramified, and universally injective. -/
theorem iff_universallyClosed_unramified_universallyInjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsClosedImmersion f ↔
      UniversallyClosed f ∧ Unramified f ∧ UniversallyInjective f :=
  sorry

/-- A morphism of algebraic spaces is a closed immersion if and only if it is
universally closed, locally of finite type, and a monomorphism. -/
theorem iff_universallyClosed_locallyOfFiniteType_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsClosedImmersion f ↔
      UniversallyClosed f ∧ LocallyOfFiniteType f ∧ Mono f :=
  sorry

/-- A morphism of algebraic spaces is a closed immersion if and only if it is
universally closed, universally injective, locally of finite type, and formally
unramified. -/
theorem iff_universallyClosed_universallyInjective_formallyUnramified
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsClosedImmersion f ↔
      UniversallyClosed f ∧ UniversallyInjective f ∧ LocallyOfFiniteType f ∧
        FormallyUnramified f :=
  sorry

/-- A closed immersion of algebraic spaces is unramified. -/
instance unramified {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsClosedImmersion f] : Unramified f :=
  sorry

/-- A closed immersion of algebraic spaces is universally injective. -/
instance universallyInjective {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsClosedImmersion f] : UniversallyInjective f :=
  sorry

/-- A universally closed unramified monomorphism of algebraic spaces is a closed
immersion. -/
instance of_universallyClosed_of_unramified_of_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [Unramified f] [Mono f] : IsClosedImmersion f :=
  sorry

end IsClosedImmersion

end AlgebraicGeometry.AlgebraicSpace
