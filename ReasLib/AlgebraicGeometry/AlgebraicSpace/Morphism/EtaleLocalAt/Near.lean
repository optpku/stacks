/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocalAt.RepresentedBy

/-!
# Neighbourhood étale-local properties of morphisms of algebraic spaces

A scheme-morphism property holds near a point of an algebraic-space morphism
when its étale-local lift holds after restriction to an open neighbourhood.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Scheme.Germ.MorphismProperty

/-- A morphism `f : X ⟶ Y` of algebraic spaces has the lift of a
scheme-morphism property `P` near a point `x` of `X` if some open subspace
neighbourhood of `x` has `etaleLocal P`. -/
def etaleLocalNear {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ etaleLocal P (i ≫ f)

/-- Having the lift of `P` near a point is the existence of an open subspace
neighbourhood on which `etaleLocal P` holds. -/
theorem etaleLocalNear_iff {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    etaleLocalNear P f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
          etaleLocal P (i ≫ f) :=
  sorry

namespace etaleLocalNear

/-- An open immersion `i : X' ⟶ X` whose composite `i ≫ f` has `etaleLocal P`
witnesses that `f` has the lift of `P` near every point of the image of `|X'|`. -/
theorem of {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} {X' : AlgebraicSpace S} {i : X' ⟶ X}
    [IsOpenImmersion i] (hx : x ∈ Set.range (Points.map i))
    (hP : etaleLocal P (i ≫ f)) : etaleLocalNear P f x :=
  sorry

/-- A morphism satisfying `etaleLocalNear P f x` admits an open subspace
neighbourhood of `x` on which `etaleLocal P` holds. -/
theorem spec {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} (h : etaleLocalNear P f x) :
    ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
      IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
        etaleLocal P (i ≫ f) :=
  sorry

end etaleLocalNear

/-- For a scheme-morphism property `P` étale local on source-and-target,
having its lift near `x` is equivalent to the associated germ-morphism
property `representedBy P` holding at `x`. -/
theorem etaleLocalNear_iff_existsEtaleSquareAt {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [IsEtaleLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    etaleLocalNear P f x ↔ existsEtaleSquareAt (representedBy P) f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
