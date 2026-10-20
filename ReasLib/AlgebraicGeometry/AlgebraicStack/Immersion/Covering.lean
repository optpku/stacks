/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Representable.Covering

/-!
# Testing immersions of algebraic stacks on an fppf covering

An immersion, open immersion, or closed immersion of algebraic stacks can be
tested after base change along a surjective, flat, locally finitely presented
morphism from an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace OpenImmersion

/-- A morphism of algebraic stacks is an open immersion if and only if
its base change along a surjective, flat, locally finitely presented morphism
from an algebraic space is represented by an open immersion of algebraic
spaces. -/
theorem iff_of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    OpenImmersion f ↔
      ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
        RepresentsTwoFibreProductOnSpace f g V W v ∧
          AlgebraicSpace.IsOpenImmersion v :=
  sorry

/-- If `v : V ⟶ W` represents the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f`, then `f` is an open immersion if and
only if `v` is an open immersion of algebraic spaces. -/
theorem iff_of_representing {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    OpenImmersion f ↔ AlgebraicSpace.IsOpenImmersion v :=
  sorry

/-- If a morphism of algebraic spaces representing the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f` is an open immersion, then `f` is an open
immersion. -/
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    AlgebraicSpace.IsOpenImmersion v → OpenImmersion f :=
  sorry

/-- If `f` is an open immersion, then a morphism of algebraic spaces representing
the 2-fibre product of `g : W.toGroupoids ⟶ Y` against `f` is an open
immersion. -/
theorem covering_spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [OpenImmersion f]
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    AlgebraicSpace.IsOpenImmersion v :=
  sorry

/-- If `f` is an open immersion, then the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f` is an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_apex {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [OpenImmersion f] {W : AlgebraicSpace S}
    (g : W.toGroupoids ⟶ Y) [Surjective g] [Flat g]
    [LocallyOfFinitePresentation g] :
    IsRepresentableByAlgebraicSpace
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f) :=
  sorry

end OpenImmersion

namespace ClosedImmersion

/-- A morphism of algebraic stacks is a closed immersion if and only if
its base change along a surjective, flat, locally finitely presented morphism
from an algebraic space is represented by a closed immersion of algebraic
spaces. -/
theorem iff_of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    ClosedImmersion f ↔
      ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
        RepresentsTwoFibreProductOnSpace f g V W v ∧
          AlgebraicSpace.IsClosedImmersion v :=
  sorry

/-- If `v : V ⟶ W` represents the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f`, then `f` is a closed immersion if and
only if `v` is a closed immersion of algebraic spaces. -/
theorem iff_of_representing {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    ClosedImmersion f ↔ AlgebraicSpace.IsClosedImmersion v :=
  sorry

/-- If a morphism of algebraic spaces representing the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f` is a closed immersion, then `f` is a closed
immersion. -/
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    AlgebraicSpace.IsClosedImmersion v → ClosedImmersion f :=
  sorry

/-- If `f` is a closed immersion, then a morphism of algebraic spaces representing
the 2-fibre product of `g : W.toGroupoids ⟶ Y` against `f` is a closed
immersion. -/
theorem covering_spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [ClosedImmersion f]
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    AlgebraicSpace.IsClosedImmersion v :=
  sorry

/-- If `f` is a closed immersion, then the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f` is an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_apex {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [ClosedImmersion f] {W : AlgebraicSpace S}
    (g : W.toGroupoids ⟶ Y) [Surjective g] [Flat g]
    [LocallyOfFinitePresentation g] :
    IsRepresentableByAlgebraicSpace
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f) :=
  sorry

end ClosedImmersion

namespace Immersion

/-- A morphism of algebraic stacks is an immersion if and only if its base
change along a surjective, flat, locally finitely presented morphism from an
algebraic space is represented by an immersion of algebraic spaces. -/
theorem iff_of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    Immersion f ↔
      ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
        RepresentsTwoFibreProductOnSpace f g V W v ∧
          AlgebraicSpace.IsImmersion v :=
  sorry

end Immersion

end AlgebraicGeometry.Groupoids.Hom
