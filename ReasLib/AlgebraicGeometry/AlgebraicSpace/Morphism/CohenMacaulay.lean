/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocalAt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.LocallyNoetherian

/-!
# Cohen–Macaulay morphisms of algebraic spaces

Pointwise Cohen–Macaulayness is flatness together with Cohen–Macaulay fibre
stalks on an étale scheme square. Global Cohen–Macaulayness is the corresponding
pointwise property and can be characterized by geometric fibre rings.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry MorphismProperty
open Scheme.Germ.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces is Cohen–Macaulay at a point `x`
of `X` if it is flat at `x` and some étale scheme square through `x` has
Cohen–Macaulay fibre stalk. -/
def CohenMacaulayAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  FlatAt f x ∧ existsEtaleSquareAt fiberStalkCohenMacaulay f x

/-- Cohen–Macaulayness at a point unpacks as flatness at that point together
with an étale scheme square whose induced germ morphism has Cohen–Macaulay
fibre stalk. -/
theorem cohenMacaulayAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    CohenMacaulayAt f x ↔
      FlatAt f x ∧ existsEtaleSquareAt fiberStalkCohenMacaulay f x :=
  sorry

/-- Pointwise Cohen–Macaulayness is equivalent to flatness at the point together
with the fibre-stalk Cohen–Macaulay property on every étale scheme square
through that point. -/
theorem cohenMacaulayAt_iff_forallEtaleSquareAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    CohenMacaulayAt f x ↔
      FlatAt f x ∧ forallEtaleSquareAt fiberStalkCohenMacaulay f x :=
  sorry

/-- The germ morphism induced by a morphism of schemes over `S` has Cohen–Macaulay
fibre stalk if and only if the fibre stalk of the underlying scheme morphism at
the distinguished source point is a Cohen–Macaulay ring. -/
theorem fiberStalkCohenMacaulay_ofOverGermHom_iff {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (u : U.left) :
    fiberStalkCohenMacaulay (ofOverGermHom h u) ↔
      CohenMacaulayRing (h.left.fiberStalkAt u) :=
  sorry

namespace CohenMacaulayAt

/-- A morphism that is Cohen–Macaulay at a point is flat there. -/
theorem flatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} (h : CohenMacaulayAt f x) : FlatAt f x :=
  sorry

/-- Flatness at `x` together with an étale scheme square through `x` whose
induced germ morphism has Cohen–Macaulay fibre stalk witnesses
`CohenMacaulayAt f x`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {x : Points X}
    (hflat : FlatAt f x)
    (hQ : existsEtaleSquareAt fiberStalkCohenMacaulay f x) :
    CohenMacaulayAt f x :=
  sorry

end CohenMacaulayAt

/-- A morphism `f : X ⟶ Y` of algebraic spaces is Cohen–Macaulay if it is
Cohen–Macaulay at every point of `X`. -/
class CohenMacaulay {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop where
  /-- The morphism is Cohen–Macaulay at every point of the source. -/
  pointwise : ∀ x : Points X, CohenMacaulayAt f x

/-- A morphism of algebraic spaces is Cohen–Macaulay if and only if it is
Cohen–Macaulay at every point of its source. -/
theorem cohenMacaulay_iff_forall_cohenMacaulayAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    CohenMacaulay f ↔ ∀ x : Points X, CohenMacaulayAt f x :=
  sorry

namespace CohenMacaulay

/-- A Cohen–Macaulay morphism of algebraic spaces is Cohen–Macaulay at every
point of its source, and in particular flat. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [CohenMacaulay f] :
    (∀ x : Points X, CohenMacaulayAt f x) ∧ Flat f :=
  sorry

/-- Every Cohen–Macaulay morphism of algebraic spaces is flat. -/
instance instFlat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [CohenMacaulay f] : Flat f :=
  sorry

/-- The identity morphism of an algebraic space is Cohen–Macaulay. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : CohenMacaulay (𝟙 X) :=
  sorry

/-- A Cohen–Macaulay morphism of schemes over `S` is Cohen–Macaulay as a
morphism of algebraic spaces. -/
instance ofOverMap {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.CohenMacaulay h.left] : CohenMacaulay (ofOverMap h) :=
  sorry

end CohenMacaulay

/-- The fibres of the base change `X_V ⟶ V` along a morphism from a scheme are
Cohen–Macaulay algebraic spaces. -/
def fibersCohenMacaulay {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : ofOver V ⟶ Y) : Prop :=
  ∀ v : V.left,
    hasEtaleLocal (Scheme.CohenMacaulay : ObjectProperty Scheme.{u})
      (residueFiberOver (pullbackAlongScheme.snd f b) (𝟙 (ofOver V)) v)

/-- `fibersCohenMacaulay f b` unpacks as Cohen–Macaulayness of every
residue-field fibre of `pullbackAlongScheme.snd f b`. -/
theorem fibersCohenMacaulay_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over S} (b : ofOver V ⟶ Y) :
    fibersCohenMacaulay f b ↔
      ∀ v : V.left,
        hasEtaleLocal (Scheme.CohenMacaulay : ObjectProperty Scheme.{u})
          (residueFiberOver (pullbackAlongScheme.snd f b) (𝟙 (ofOver V)) v) :=
  sorry

namespace fibersCohenMacaulay

/-- If the fibres of `X_V ⟶ V` are Cohen–Macaulay, then the residue-field fibre
at `v` is a Cohen–Macaulay algebraic space. -/
theorem apply {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {V : Over S}
    {b : ofOver V ⟶ Y} (h : fibersCohenMacaulay f b) (v : V.left) :
    hasEtaleLocal (Scheme.CohenMacaulay : ObjectProperty Scheme.{u})
      (residueFiberOver (pullbackAlongScheme.snd f b) (𝟙 (ofOver V)) v) :=
  sorry

end fibersCohenMacaulay

/-- Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume the fibres of `f` are locally Noetherian.
The following are equivalent: `f` is Cohen–Macaulay; `f` is flat and for some
surjective étale morphism `V ⟶ Y` with `V` a scheme, the fibres of `X_V ⟶ V`
are Cohen–Macaulay algebraic spaces; and `f` is flat and for any étale
morphism `V ⟶ Y` with `V` a scheme, the fibres of `X_V ⟶ V` are Cohen–Macaulay
algebraic spaces. -/
@[stacks 0E0W]
theorem cohenMacaulay_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyNoetherianFibers f] :
    List.TFAE
      [ CohenMacaulay f
      , Flat f ∧
          ∃ (V : Over S) (b : ofOver V ⟶ Y),
            (over (@AlgebraicGeometry.Etale)).presheaf b ∧
              Surjective b ∧ fibersCohenMacaulay f b
      , Flat f ∧
          ∀ (V : Over S) (b : ofOver V ⟶ Y),
            (over (@AlgebraicGeometry.Etale)).presheaf b →
              fibersCohenMacaulay f b ] :=
  sorry

/-- Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume the fibres of `f` are locally Noetherian.
Given `x` in `|X|` with image `y = Points.map f x` in `|Y|`, `f` is
Cohen–Macaulay at `x` if and only if
`etaleLocalRingMap f xbar : 𝒪_{Y, ȳ} ⟶ 𝒪_{X, x̄}` is flat and
`fiberEtaleLocalRing f xbar` is a Cohen–Macaulay ring, for a geometric point
`xbar` lying over `x`. -/
@[stacks 0E0W]
theorem cohenMacaulayAt_iff_etaleLocalRing {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyNoetherianFibers f]
    (xbar : GeometricPoint X) (x : Points X) (hx : xbar.liesOver x) :
    CohenMacaulayAt f x ↔
      (etaleLocalRingMap f xbar).Flat ∧
        CohenMacaulayRing (fiberEtaleLocalRing f xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
