/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Pointwise etaleness of morphisms of algebraic spaces

A morphism of algebraic spaces is etale at a point when it is etale after
restriction to an open subspace neighbourhood.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces is etale at a point `x` of `X`
if it is etale after restriction to some open subspace neighbourhood of `x`. -/
def EtaleAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Etale (i ≫ f)

/-- Etaleness at a point is the existence of an open subspace neighbourhood on
which the morphism is etale. -/
theorem etaleAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    EtaleAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Etale (i ≫ f) :=
  sorry

namespace EtaleAt

/-- An open immersion `i : X' ⟶ X` whose composite `i ≫ f` is etale witnesses
that `f` is etale at every point of the image of `|X'|`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} {X' : AlgebraicSpace S} {i : X' ⟶ X}
    [IsOpenImmersion i] (hx : x ∈ Set.range (Points.map i))
    [Etale (i ≫ f)] : EtaleAt f x :=
  sorry

end EtaleAt

/-- An etale morphism of algebraic spaces is etale at every point of its source. -/
theorem etaleAt_of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] (x : Points X) : EtaleAt f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
