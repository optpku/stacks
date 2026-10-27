/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Gorenstein
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein.Global

/-!
# Gorenstein algebraic spaces and morphisms

The source spelling of pointwise Gorensteinness is retained as a transparent
abbreviation for the canonical predicate.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty
open Scheme.Germ.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism is Gorenstein at a point when its canonical pointwise
Gorenstein predicate holds. -/
abbrev gorensteinAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  GorensteinAt f x

#check (AlgebraicGeometry.AlgebraicSpace.Gorenstein :
  {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IsGorenstein :
  {S : Scheme.{u}} → AlgebraicSpace S → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.gorensteinAt_iff_flat_and_existsEtaleSquareAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X),
    GorensteinAt f x ↔
      FlatAt f x ∧ existsEtaleSquareAt fiberStalkGorenstein f x)

#check (AlgebraicGeometry.AlgebraicSpace.gorensteinAt_iff_forallEtaleSquareAt :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X),
    GorensteinAt f x ↔
      FlatAt f x ∧ forallEtaleSquareAt fiberStalkGorenstein f x)

#check (AlgebraicGeometry.AlgebraicSpace.Gorenstein.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Gorenstein f] (x : Points X), GorensteinAt f x)

#check (AlgebraicGeometry.AlgebraicSpace.Gorenstein.of :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ x : Points X, GorensteinAt f x), Gorenstein f)

#check (AlgebraicGeometry.AlgebraicSpace.Gorenstein.gorenstein_iff_forall_gorensteinAt :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Gorenstein f ↔ ∀ x : Points X, GorensteinAt f x)

#check (AlgebraicGeometry.AlgebraicSpace.Gorenstein.instFlat :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Gorenstein f], Flat f)

#check (AlgebraicGeometry.AlgebraicSpace.instGorenstein_ofOverMap :
  ∀ {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.Gorenstein h.left], Gorenstein (ofOverMap h))

#check (AlgebraicGeometry.AlgebraicSpace.IsGorenstein.spec :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsGorenstein X],
    existsSurjectiveEtale (Scheme.Gorenstein : ObjectProperty Scheme.{u}) X)

#check (AlgebraicGeometry.AlgebraicSpace.IsGorenstein.of :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : existsSurjectiveEtale (Scheme.Gorenstein : ObjectProperty Scheme.{u}) X),
    IsGorenstein X)

#check (AlgebraicGeometry.AlgebraicSpace.instIsGorenstein_ofOver :
  ∀ {S : Scheme.{u}} (T : Over S)
    [Scheme.Gorenstein T.left], IsGorenstein (ofOver T))

#check (AlgebraicGeometry.AlgebraicSpace.isGorenstein_iff_forallEtale :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    IsGorenstein X ↔
      forallEtale (Scheme.Gorenstein : ObjectProperty Scheme.{u}) X)

#check (AlgebraicGeometry.AlgebraicSpace.gorensteinAt_ofOverMap_iff :
  ∀ {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) (u : U.left),
    GorensteinAt (ofOverMap h) (ofOver.pointsEquiv U u) ↔
      Scheme.Hom.gorensteinAt h.left u)

end AlgebraicGeometry.AlgebraicSpace
