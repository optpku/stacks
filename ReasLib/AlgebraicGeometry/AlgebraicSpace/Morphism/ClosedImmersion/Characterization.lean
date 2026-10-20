/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed

/-!
# Characterizations of closed immersions of algebraic spaces

Closed immersions are characterized by universal closedness together with
unramifiedness, monicity, universal injectivity, and local finite type conditions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a morphism of algebraic spaces, being a closed immersion is equivalent
to universal closedness together with any of: unramified monicity; unramified
universal injectivity; locally finite type monicity; or universally injective,
locally finite type formal unramifiedness. -/
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
  (tfae_isClosedImmersion f).out 0 1

/-- A morphism of algebraic spaces is a closed immersion if and only if it is
universally closed, unramified, and universally injective. -/
theorem iff_universallyClosed_unramified_universallyInjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsClosedImmersion f ↔
      UniversallyClosed f ∧ Unramified f ∧ UniversallyInjective f :=
  (tfae_isClosedImmersion f).out 0 2

/-- A morphism of algebraic spaces is a closed immersion if and only if it is
universally closed, locally of finite type, and a monomorphism. -/
theorem iff_universallyClosed_locallyOfFiniteType_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsClosedImmersion f ↔
      UniversallyClosed f ∧ LocallyOfFiniteType f ∧ Mono f :=
  (tfae_isClosedImmersion f).out 0 3

/-- A morphism of algebraic spaces is a closed immersion if and only if it is
universally closed, universally injective, locally of finite type, and formally
unramified. -/
theorem iff_universallyClosed_universallyInjective_formallyUnramified
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsClosedImmersion f ↔
      UniversallyClosed f ∧ UniversallyInjective f ∧ LocallyOfFiniteType f ∧
        FormallyUnramified f :=
  (tfae_isClosedImmersion f).out 0 4

/-- A closed immersion of algebraic spaces is universally injective. -/
instance universallyInjective {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsClosedImmersion f] : UniversallyInjective f :=
  ((iff_universallyClosed_unramified_universallyInjective f).mp inferInstance).2.2

/-- A universally closed unramified monomorphism of algebraic spaces is a closed
immersion. -/
instance of_universallyClosed_of_unramified_of_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [Unramified f] [Mono f] : IsClosedImmersion f :=
  (iff_universallyClosed_unramified_mono f).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

end IsClosedImmersion

end AlgebraicGeometry.AlgebraicSpace
