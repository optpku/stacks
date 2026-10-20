/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Étale-local characterizations of formal unramifiedness

Formal unramifiedness of a morphism of algebraic spaces can be tested on
commutative squares with étale vertical arrows from schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallyUnramified

/-- A formally unramified morphism of algebraic spaces has formally unramified
top arrow on every commutative square with étale vertical arrows from schemes. -/
theorem etaleSchemeSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {U V : Over S} {h : U ⟶ V} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y}
    {f : X ⟶ Y} [FormallyUnramified f] [Etale a] [Etale b]
    (sq : CommSq (ofOverMap h) a b f) :
    AlgebraicGeometry.FormallyUnramified h.left := sorry

/-- A morphism of algebraic spaces is formally unramified if a commutative square
with étale vertical arrows surjective on points has formally unramified top arrow. -/
theorem of_surjectiveEtaleSchemeSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {U V : Over S} {h : U ⟶ V} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y} {f : X ⟶ Y}
    [Etale a] [Etale b]
    (ha_surjective : Function.Surjective (Points.map a))
    (hb_surjective : Function.Surjective (Points.map b))
    [AlgebraicGeometry.FormallyUnramified h.left]
    (sq : CommSq (ofOverMap h) a b f) : FormallyUnramified f := sorry

/-- On a commutative square with étale vertical arrows surjective on points,
formal unramifiedness of the bottom arrow is equivalent to formal unramifiedness
of the top arrow as a morphism of schemes. -/
theorem iff_of_surjectiveEtaleSchemeSquare {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {U V : Over S} {h : U ⟶ V} {a : ofOver U ⟶ X}
    {b : ofOver V ⟶ Y} {f : X ⟶ Y} [Etale a] [Etale b]
    (ha_surjective : Function.Surjective (Points.map a))
    (hb_surjective : Function.Surjective (Points.map b))
    (sq : CommSq (ofOverMap h) a b f) :
    FormallyUnramified f ↔ AlgebraicGeometry.FormallyUnramified h.left := sorry

/-- A morphism of algebraic spaces is formally unramified if and only if every
commutative square with étale vertical arrows from schemes has formally
unramified top arrow as a morphism of schemes. -/
theorem iff_forall_etaleSchemeSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FormallyUnramified f ↔
      ∀ {U V : Over S} (h : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
        [Etale a] [Etale b], CommSq (ofOverMap h) a b f →
          AlgebraicGeometry.FormallyUnramified h.left := sorry

/-- A morphism of algebraic spaces is formally unramified if and only if there
is a commutative square with étale vertical arrows from schemes surjective on
points whose top arrow is formally unramified as a morphism of schemes. -/
theorem iff_exists_surjectiveEtaleSchemeSquare {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    FormallyUnramified f ↔
      ∃ (U V : Over S) (h : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y),
        Etale a ∧ Etale b ∧ Function.Surjective (Points.map a) ∧
          Function.Surjective (Points.map b) ∧ CommSq (ofOverMap h) a b f ∧
            AlgebraicGeometry.FormallyUnramified h.left := sorry

/-- On a commutative square of algebraic spaces with étale vertical arrows, the
top arrow is formally unramified as soon as the bottom arrow is. -/
theorem of_etaleCommSq {S : Scheme.{u}} {X Z U V : AlgebraicSpace S}
    (fVU : V ⟶ U) (fVZ : V ⟶ Z) (fUX : U ⟶ X) (h : Z ⟶ X)
    [FormallyUnramified h] [Etale fVZ] [Etale fUX]
    (sq : CommSq fVU fVZ fUX h) : FormallyUnramified fVU :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormallyUnramified
