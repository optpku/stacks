/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein.Locus

/-!
# Gorenstein loci of morphisms of algebraic spaces

The Gorenstein locus of a flat, locally finitely presented morphism of
algebraic spaces is open and commutes with arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The locus of points of `X` at which `f` is Gorenstein. -/
def gorensteinLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Set (Points X) :=
  {x | GorensteinAt f x}

/-- A point lies in the Gorenstein locus exactly when the morphism is
Gorenstein at that point. -/
theorem mem_gorensteinLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    x ∈ gorensteinLocus f ↔ GorensteinAt f x :=
  sorry

/-- Along an étale scheme square over `f`, the preimage of `gorensteinLocus f`
is the scheme-level Gorenstein locus of the top arrow. -/
theorem mapOfOver_preimage_gorensteinLocus {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) {U V : Over S} (a : ofOver U ⟶ X)
    (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) :
    Points.mapOfOver a ⁻¹' gorensteinLocus f =
      Scheme.Hom.gorensteinLocus h.left :=
  sorry

/-- The Gorenstein locus of a flat, locally finitely presented morphism of
algebraic spaces is open. -/
theorem isOpen_gorensteinLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] :
    IsOpen (gorensteinLocus f) :=
  sorry

/-- The Gorenstein locus of a flat, locally finitely presented morphism of
algebraic spaces commutes with arbitrary base change. -/
theorem gorensteinLocus_pullback_snd {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] (g : Y' ⟶ Y) :
    gorensteinLocus (pullback.snd f g) =
      Points.map (pullback.fst f g) ⁻¹' gorensteinLocus f :=
  sorry

/-- A base change of a flat, locally finitely presented morphism of algebraic
spaces is Gorenstein at a point if and only if the original morphism is
Gorenstein at its image under the projection. -/
theorem gorensteinAt_iff_of_pullback_snd {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] (g : Y' ⟶ Y)
    (x' : Points (pullback f g)) :
    GorensteinAt (pullback.snd f g) x' ↔
      GorensteinAt f (Points.map (pullback.fst f g) x') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
