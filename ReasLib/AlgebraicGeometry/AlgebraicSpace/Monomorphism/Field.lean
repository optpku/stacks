/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A monomorphism of algebraic spaces over a scheme toward the spectrum of a field
has empty source or is an isomorphism. -/
@[stacks 06MG]
theorem isEmpty_or_isIso_of_mono_over_field {S : Scheme.{u}} {k : Type u} [Field k]
    {X : AlgebraicSpace S} (σ : Spec (CommRingCat.of k) ⟶ S)
    (f : X ⟶ ofOver (Over.mk σ)) [Mono f] :
    IsEmpty (Points X) ∨ IsIso f := sorry

/-- A monomorphism of algebraic spaces over a scheme toward the spectrum of a field
is an isomorphism if and only if its source has a point. -/
theorem isIso_iff_nonempty_of_mono_over_field {S : Scheme.{u}} {k : Type u} [Field k]
    {X : AlgebraicSpace S} (σ : Spec (CommRingCat.of k) ⟶ S)
    (f : X ⟶ ofOver (Over.mk σ)) [Mono f] :
    IsIso f ↔ Nonempty (Points X) := sorry

/-- A monomorphism of algebraic spaces over a scheme into a target admitting a
locally finitely presented, surjective, flat morphism from the spectrum of a
field has empty source or is an isomorphism. -/
@[stacks 06QY]
theorem isEmpty_or_isIso_of_mono_of_spec_field_fppf {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Mono f] {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (g : ofOver (Over.mk σ) ⟶ Y)
    [LocallyOfFinitePresentation g] [Surjective g] [Flat g] :
    IsEmpty (Points X) ∨ IsIso f := sorry

/-- A monomorphism of algebraic spaces over a scheme into a target admitting a
locally finitely presented, surjective, flat morphism from the spectrum of a
field is an isomorphism if and only if its source has a point. -/
theorem isIso_iff_nonempty_of_mono_of_spec_field_fppf {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Mono f] {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (g : ofOver (Over.mk σ) ⟶ Y)
    [LocallyOfFinitePresentation g] [Surjective g] [Flat g] :
    IsIso f ↔ Nonempty (Points X) := sorry

end AlgebraicGeometry.AlgebraicSpace
