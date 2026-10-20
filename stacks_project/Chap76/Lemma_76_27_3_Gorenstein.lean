/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein
public import stacks_project.Chap66.Lemma_66_7_1
public import stacks_project.Chap66.Remark_66_7_3_EtaleLocal
public import stacks_project.Chap67.Lemma_67_22_5
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Lemma_76_27_1_FiberStalk

/-!
# Gorenstein morphisms of algebraic spaces

A morphism of algebraic spaces is Gorenstein at a point when it is flat there and
some étale scheme square through that point has Gorenstein fibre stalk, in the
sense of Stacks Definition 76.27.2. A Gorenstein algebraic space is one that
admits a representable étale locally-surjective atlas from a Gorenstein scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty
open Scheme.Germ.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces is Gorenstein at a point `x` of
`X` if it is flat at `x` and some étale scheme square through `x` has Gorenstein
fibre stalk. -/
def gorensteinAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  FlatAt f x ∧ existsEtaleSquareAt fiberStalkGorenstein f x

/-- Pointwise Gorensteinness is flatness at the point together with the existence
of an étale scheme square through that point with Gorenstein fibre stalk. -/
theorem gorensteinAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    gorensteinAt f x ↔
      FlatAt f x ∧ existsEtaleSquareAt fiberStalkGorenstein f x :=
  sorry

/-- Pointwise Gorensteinness is equivalent to flatness at the point together with
the fibre-stalk Gorenstein property on every étale scheme square through that
point. -/
theorem gorensteinAt_iff_forallEtaleSquareAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    gorensteinAt f x ↔
      FlatAt f x ∧ forallEtaleSquareAt fiberStalkGorenstein f x :=
  sorry

/-- A morphism of schemes over `S`, viewed as a morphism of algebraic spaces, is
Gorenstein at the image of `u` if and only if the underlying morphism of schemes
is Gorenstein at `u`. -/
theorem ofOverMap_gorensteinAt_iff {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    (u : U.left) :
    gorensteinAt (ofOverMap h) (ofOver.pointsEquiv U u) ↔
      Scheme.Hom.gorensteinAt h.left u :=
  sorry

/-- The germ morphism induced by a morphism of schemes over `S` has Gorenstein
fibre stalk if and only if the fibre stalk of the underlying scheme morphism at
the distinguished source point is a Gorenstein local ring. -/
theorem fiberStalkGorenstein_ofOverGermHom_iff {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (u : U.left) :
    fiberStalkGorenstein (ofOverGermHom h u) ↔
      IsGorensteinLocalRing (Scheme.Hom.fiberStalkAt h.left u) :=
  sorry

/-- A morphism of algebraic spaces is Gorenstein if it is Gorenstein at every
point of the source. -/
class Gorenstein {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- A Gorenstein morphism is Gorenstein at every source point. -/
  gorensteinAt_forall : ∀ x : Points X, gorensteinAt f x

namespace Gorenstein

/-- A Gorenstein morphism of algebraic spaces is Gorenstein at every source
point. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Gorenstein f] (x : Points X) : gorensteinAt f x :=
  sorry

/-- A morphism of algebraic spaces that is Gorenstein at every source point is a
Gorenstein morphism. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ x : Points X, gorensteinAt f x) : Gorenstein f :=
  sorry

/-- A morphism of algebraic spaces is Gorenstein if and only if it is Gorenstein
at every source point. -/
theorem gorenstein_iff_forall_gorensteinAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Gorenstein f ↔ ∀ x : Points X, gorensteinAt f x :=
  sorry

/-- A Gorenstein morphism of algebraic spaces is flat. -/
instance instFlat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Gorenstein f] : Flat f :=
  sorry

end Gorenstein

/-- A morphism of schemes over `S` that is Gorenstein remains Gorenstein after
viewing it as a morphism of algebraic spaces. -/
instance instGorenstein_ofOverMap {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.Gorenstein h.left] : Gorenstein (ofOverMap h) where
  gorensteinAt_forall := sorry

/-- An algebraic space is Gorenstein if it admits a representable étale
locally-surjective atlas from a Gorenstein scheme. -/
@[mk_iff]
class IsGorenstein {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- There is a representable étale locally-surjective atlas from a Gorenstein
  scheme. -/
  exists_gorenstein_etaleCover :
    existsSurjectiveEtale (Scheme.Gorenstein : ObjectProperty Scheme.{u}) X

namespace IsGorenstein

/-- A Gorenstein algebraic space admits a representable étale locally-surjective
atlas from a Gorenstein scheme. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsGorenstein X] :
    existsSurjectiveEtale (Scheme.Gorenstein : ObjectProperty Scheme.{u}) X :=
  sorry

/-- A representable étale locally-surjective atlas from a Gorenstein scheme
witnesses that the algebraic space is Gorenstein. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : existsSurjectiveEtale (Scheme.Gorenstein : ObjectProperty Scheme.{u}) X) :
    IsGorenstein X :=
  sorry

end IsGorenstein

/-- A Gorenstein scheme over `S`, viewed as an algebraic space, is Gorenstein. -/
instance instIsGorenstein_ofOver {S : Scheme.{u}} (T : Over S)
    [Scheme.Gorenstein T.left] : IsGorenstein (ofOver T) where
  exists_gorenstein_etaleCover :=
    (existsSurjectiveEtale_ofOver (Scheme.Gorenstein : ObjectProperty Scheme.{u}) T).mpr
      inferInstance

/-- An algebraic space is Gorenstein if and only if every étale morphism from a
scheme to it has Gorenstein source. -/
theorem isGorenstein_iff_forallEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsGorenstein X ↔
      forallEtale (Scheme.Gorenstein : ObjectProperty Scheme.{u}) X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
