/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Monomorphism
import StacksCheckRecall

/-!
# Unramified monomorphisms of algebraic spaces

A morphism of algebraic spaces is unramified and a monomorphism if and only if
it is unramified and universally injective, if and only if it is locally of
finite type and a monomorphism, if and only if it is universally injective,
locally of finite type, and formally unramified. In this case it is also
representable, separated, and locally quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.14.8 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is unramified and
a monomorphism; `f` is unramified and universally injective; `f` is locally of
finite type and a monomorphism; `f` is universally injective, locally of finite
type, and formally unramified. -/
@[stacks 05W6] #check (AlgebraicGeometry.AlgebraicSpace.tfae_unramified_mono :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [
      Unramified f ∧ Mono f,
      Unramified f ∧ UniversallyInjective f,
      LocallyOfFiniteType f ∧ Mono f,
      UniversallyInjective f ∧ LocallyOfFiniteType f ∧ FormallyUnramified f])

/- Lemma 76.14.8 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is unramified and a monomorphism, then `f` is
representable. -/
@[stacks 05W6] #check (AlgebraicGeometry.AlgebraicSpace.relativelyRepresentable_of_unramified_of_mono :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Unramified f] [Mono f], yoneda.relativelyRepresentable f)

/- Lemma 76.14.8 (3): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is unramified and universally injective, then
`f` is separated. -/
@[stacks 05W6] #check (AlgebraicGeometry.AlgebraicSpace.separated_of_unramified_of_universallyInjective :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Unramified f] [UniversallyInjective f], Separated f)

/- Lemma 76.14.8 (4): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is unramified and a monomorphism, then `f` is
locally quasi-finite. -/
@[stacks 05W6] #check (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_of_unramified_of_mono :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Unramified f] [Mono f], LocallyQuasiFinite f)

#check (AlgebraicGeometry.AlgebraicSpace.unramified_mono_iff_universallyInjective :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Unramified f ∧ Mono f ↔ Unramified f ∧ UniversallyInjective f)

#check (AlgebraicGeometry.AlgebraicSpace.unramified_mono_iff_locallyOfFiniteType_mono :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Unramified f ∧ Mono f ↔ LocallyOfFiniteType f ∧ Mono f)

#check (AlgebraicGeometry.AlgebraicSpace.unramified_mono_iff_formallyUnramified :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Unramified f ∧ Mono f ↔
      UniversallyInjective f ∧ LocallyOfFiniteType f ∧ FormallyUnramified f)

#check (AlgebraicGeometry.AlgebraicSpace.mono_of_unramified_of_universallyInjective :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Unramified f] [UniversallyInjective f], Mono f)

#check (AlgebraicGeometry.AlgebraicSpace.unramified_of_locallyOfFiniteType_of_mono :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Mono f], Unramified f)

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.mono_iff_universallyInjective :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Unramified f], Mono f ↔ UniversallyInjective f)

end AlgebraicGeometry.AlgebraicSpace
