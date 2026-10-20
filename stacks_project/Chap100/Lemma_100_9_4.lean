/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Immersion.Covering
import StacksCheckRecall

/-!
# Testing immersions of algebraic stacks on one fppf covering

For a morphism of algebraic stacks, being an immersion, an open immersion, or
a closed immersion is equivalent to its base change to one surjective, flat,
locally finitely presented algebraic-space covering being an algebraic space
whose projection has the corresponding immersion property.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

universe u

/- Lemma 100.9.4: A morphism of algebraic stacks is an open immersion
if and only if its base change to a surjective, flat, locally finitely presented
algebraic-space covering is an algebraic space with the same immersion property. -/
@[stacks 0503]
#check (AlgebraicGeometry.Groupoids.Hom.OpenImmersion.iff_of_covering :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g],
    OpenImmersion f ↔
      ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
        RepresentsTwoFibreProductOnSpace f g V W v ∧
          AlgebraicSpace.IsOpenImmersion v)

#check (AlgebraicGeometry.Groupoids.Hom.OpenImmersion.iff_of_representing :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v),
    OpenImmersion f ↔ AlgebraicSpace.IsOpenImmersion v)

#check (AlgebraicGeometry.Groupoids.Hom.OpenImmersion.of_covering :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v),
    AlgebraicSpace.IsOpenImmersion v → OpenImmersion f)

#check (AlgebraicGeometry.Groupoids.Hom.OpenImmersion.covering_spec :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [OpenImmersion f]
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v),
    AlgebraicSpace.IsOpenImmersion v)

#check (AlgebraicGeometry.Groupoids.Hom.OpenImmersion.isRepresentableByAlgebraicSpace_apex :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [OpenImmersion f] {W : AlgebraicSpace S}
    (g : W.toGroupoids ⟶ Y) [Surjective g] [Flat g]
    [LocallyOfFinitePresentation g],
    IsRepresentableByAlgebraicSpace
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f))

/- Lemma 100.9.4: A morphism of algebraic stacks is a closed immersion
if and only if its base change to a surjective, flat, locally finitely presented
algebraic-space covering is an algebraic space with the same immersion property. -/
@[stacks 0503]
#check (AlgebraicGeometry.Groupoids.Hom.ClosedImmersion.iff_of_covering :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g],
    ClosedImmersion f ↔
      ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
        RepresentsTwoFibreProductOnSpace f g V W v ∧
          AlgebraicSpace.IsClosedImmersion v)

#check (AlgebraicGeometry.Groupoids.Hom.ClosedImmersion.iff_of_representing :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v),
    ClosedImmersion f ↔ AlgebraicSpace.IsClosedImmersion v)

#check (AlgebraicGeometry.Groupoids.Hom.ClosedImmersion.of_covering :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v),
    AlgebraicSpace.IsClosedImmersion v → ClosedImmersion f)

#check (AlgebraicGeometry.Groupoids.Hom.ClosedImmersion.covering_spec :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [ClosedImmersion f]
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v),
    AlgebraicSpace.IsClosedImmersion v)

#check (AlgebraicGeometry.Groupoids.Hom.ClosedImmersion.isRepresentableByAlgebraicSpace_apex :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [ClosedImmersion f] {W : AlgebraicSpace S}
    (g : W.toGroupoids ⟶ Y) [Surjective g] [Flat g]
    [LocallyOfFinitePresentation g],
    IsRepresentableByAlgebraicSpace
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f))

/- Lemma 100.9.4: A morphism of algebraic stacks is an immersion
if and only if its base change to a surjective, flat, locally finitely presented
algebraic-space covering is an algebraic space with the same immersion property. -/
@[stacks 0503]
#check (AlgebraicGeometry.Groupoids.Hom.Immersion.iff_of_covering :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g],
    Immersion f ↔
      ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
        RepresentsTwoFibreProductOnSpace f g V W v ∧
          AlgebraicSpace.IsImmersion v)
