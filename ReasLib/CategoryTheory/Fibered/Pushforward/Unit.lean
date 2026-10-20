/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward
public import ReasLib.CategoryTheory.Functor.OverIso

/-!
# The unit of pushforward for fibered categories

For `u : C ⥤ D` and `p : S ⥤ C`, the pushforward construction has a canonical functor
`S ⥤ u ₚ p`.  This module owns that functor and its projection-level interface, independently
of any bundled presentation of `p` or of a particular proof of the pushforward universal
property.
-/

@[expose] public section

universe uC uD uS vC vD vS

namespace CategoryTheory

open Limits
open scoped Functor

namespace Functor.Pushforward

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

namespace Prelocalized

/-- The object of the prelocalized pushforward selected by an object of `S`. -/
@[stacks 04WG "prelocalized pushforward unit object"]
def obj (u : C ⥤ D) (p : S ⥤ C) (x : S) : u ₚₚ p :=
  { fst :=
      { left := u.obj (p.obj x)
        right := p.obj x
        hom := 𝟙 (u.obj (p.obj x)) }
    snd := x
    iso := Iso.refl (p.obj x) }

/-- The commutative-square condition for the comma component of the prelocalized unit map. -/
@[stacks 04WG "prelocalized pushforward unit comma compatibility"]
theorem mapFst.naturality (u : C ⥤ D) (p : S ⥤ C)
    {x y : S} (f : x ⟶ y) :
    (𝟭 D).map (u.map (p.map f)) ≫ (obj u p y).fst.hom =
      (obj u p x).fst.hom ≫ u.map (p.map f) := sorry

/-- The comma-category component of the prelocalized unit map. -/
@[stacks 04WG "prelocalized pushforward unit comma map"]
def mapFst (u : C ⥤ D) (p : S ⥤ C)
    {x y : S} (f : x ⟶ y) :
    (obj u p x).fst ⟶ (obj u p y).fst where
  left := u.map (p.map f)
  right := p.map f
  w := mapFst.naturality u p f

/-- The pullback compatibility condition for the prelocalized unit map. -/
@[stacks 04WG "prelocalized pushforward unit pullback compatibility"]
theorem map.naturality (u : C ⥤ D) (p : S ⥤ C)
    {x y : S} (f : x ⟶ y) :
    (Comma.snd (𝟭 D) u).map (mapFst u p f) ≫
        (obj u p y).iso.hom =
      (obj u p x).iso.hom ≫ p.map f := sorry

/-- The morphism of the prelocalized pushforward selected by a morphism of `S`. -/
@[stacks 04WG "prelocalized pushforward unit map"]
def map (u : C ⥤ D) (p : S ⥤ C)
    {x y : S} (f : x ⟶ y) :
    obj u p x ⟶ obj u p y where
  fst := mapFst u p f
  snd := f
  w := map.naturality u p f

/-- The prelocalized unit map takes identities to identities. -/
@[stacks 04WG "prelocalized pushforward unit identity"]
theorem map.id (u : C ⥤ D) (p : S ⥤ C) (x : S) :
    map u p (𝟙 x) = 𝟙 (obj u p x) := sorry

/-- The prelocalized unit map preserves composition. -/
@[stacks 04WG "prelocalized pushforward unit composition"]
theorem map.comp (u : C ⥤ D) (p : S ⥤ C)
    {x y z : S} (f : x ⟶ y) (g : y ⟶ z) :
    map u p (f ≫ g) = map u p f ≫ map u p g := sorry

/-- The canonical functor from `S` to the prelocalized pushforward source. -/
@[stacks 04WG "prelocalized pushforward unit functor"]
def functor (u : C ⥤ D) (p : S ⥤ C) : S ⥤ u ₚₚ p where
  obj := obj u p
  map f := map u p f
  map_id := map.id u p
  map_comp := map.comp u p

namespace functor

/-- The object action of the prelocalized pushforward unit. -/
@[simp, stacks 04WG "prelocalized pushforward unit object computation"]
theorem obj (u : C ⥤ D) (p : S ⥤ C) (x : S) :
    (Prelocalized.functor u p).obj x = Prelocalized.obj u p x := sorry

/-- The morphism action of the prelocalized pushforward unit. -/
@[simp, stacks 04WG "prelocalized pushforward unit map computation"]
theorem map (u : C ⥤ D) (p : S ⥤ C)
    {x y : S} (f : x ⟶ y) :
    (Prelocalized.functor u p).map f = Prelocalized.map u p f := sorry

end functor

/-- The left component of a prelocalized unit map is the image of the base morphism under `u`. -/
@[simp, stacks 04WG "prelocalized unit comma left component"]
theorem mapFst.left (u : C ⥤ D) (p : S ⥤ C)
    {x y : S} (f : x ⟶ y) :
    (mapFst u p f).left = u.map (p.map f) := sorry

/-- The right component of a prelocalized unit map is the original base morphism. -/
@[simp, stacks 04WG "prelocalized unit comma right component"]
theorem mapFst.right (u : C ⥤ D) (p : S ⥤ C)
    {x y : S} (f : x ⟶ y) :
    (mapFst u p f).right = p.map f := sorry

/-- The first pullback component of a prelocalized unit map is its comma-category map. -/
@[simp, stacks 04WG "prelocalized unit pullback first component"]
theorem map.fst (u : C ⥤ D) (p : S ⥤ C)
    {x y : S} (f : x ⟶ y) :
    (map u p f).fst = mapFst u p f := sorry

/-- The second pullback component of a prelocalized unit map is the original morphism. -/
@[simp, stacks 04WG "prelocalized unit pullback second component"]
theorem map.snd (u : C ⥤ D) (p : S ⥤ C)
    {x y : S} (f : x ⟶ y) :
    (map u p f).snd = f := sorry

/-- The prelocalized unit followed by the source projection is the composite `p ⋙ u`. -/
@[stacks 04WG "prelocalized unit source projection"]
theorem functor.compSourceProjection (u : C ⥤ D) (p : S ⥤ C) :
    functor u p ⋙ Functor.Pushforward.sourceProjection u p = p ⋙ u := sorry

/-- Naturality of the identity components comparing the prelocalized unit projection with
`p ⋙ u`. -/
@[stacks 04WG "prelocalized unit projection naturality"]
theorem projectionIso.naturality (u : C ⥤ D) (p : S ⥤ C)
    {x y : S} (f : x ⟶ y) :
    (functor u p ⋙ Functor.Pushforward.sourceProjection u p).map f ≫
        𝟙 ((p ⋙ u).obj y) =
      𝟙 ((p ⋙ u).obj x) ≫ (p ⋙ u).map f := sorry

/-- The prelocalized unit projection comparison, with explicit identity components. Only its
naturality is proof-valued; no functor equality is converted into isomorphism data. -/
@[stacks 04WG "prelocalized unit projection isomorphism"]
def projectionIso (u : C ⥤ D) (p : S ⥤ C) :
    functor u p ⋙ Functor.Pushforward.sourceProjection u p ≅ p ⋙ u :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ projectionIso.naturality u p f)

end Prelocalized

namespace Unit

/-- The canonical functor from `S` to the localized pushforward `u ₚ p`. -/
@[stacks 04WG "localized pushforward unit functor"]
noncomputable def functor (u : C ⥤ D) (p : S ⥤ C) : S ⥤ u ₚ p :=
  Prelocalized.functor u p ⋙ (u.pushforwardFractions p).Q

namespace functor

/-- The object action of the localized pushforward unit. -/
@[simp, stacks 04WG "localized pushforward unit object computation"]
theorem obj (u : C ⥤ D) (p : S ⥤ C) (x : S) :
    (Unit.functor u p).obj x =
      (u.pushforwardFractions p).Q.obj (Prelocalized.obj u p x) := sorry

/-- The morphism action of the localized pushforward unit. -/
@[simp, stacks 04WG "localized pushforward unit map computation"]
theorem map (u : C ⥤ D) (p : S ⥤ C)
    {x y : S} (f : x ⟶ y) :
    (Unit.functor u p).map f =
      (u.pushforwardFractions p).Q.map (Prelocalized.map u p f) := sorry

end functor

/-- The localized unit followed by a projection induced by an explicit fraction-inversion proof is
the composite `p ⋙ u`. -/
@[stacks 04WG "localized unit projection comparison"]
theorem functor.compProjection (u : C ⥤ D) (p : S ⥤ C)
    (h_inverts : (u.pushforwardFractions p).IsInvertedBy
      (Functor.Pushforward.sourceProjection u p)) :
    functor u p ⋙ Functor.Pushforward.projection u p h_inverts = p ⋙ u := sorry

/-- The localized unit followed by an explicitly chosen pushforward projection is the base
composite `p ⋙ u`. -/
@[stacks 04WG "localized unit chosen projection comparison"]
theorem functor.compPushforwardProjection (u : C ⥤ D) (p : S ⥤ C)
    (h : Functor.Pushforward.ProjectionChoice u p) :
    functor u p ⋙ u.pushforwardProjection p h = p ⋙ u := sorry

namespace Explicit

/-- The localized unit projection comparison induced by an explicit proof that the source
projection inverts the pushforward fractions. The localization comparison is owned by the
generic pushforward projection API and is whiskered with the prelocalized unit comparison. -/
@[stacks 04WG "explicit localized unit projection isomorphism"]
noncomputable def projectionIso (u : C ⥤ D) (p : S ⥤ C)
    (h_inverts : (u.pushforwardFractions p).IsInvertedBy
      (Functor.Pushforward.sourceProjection u p)) :
    functor u p ⋙ Functor.Pushforward.projection u p h_inverts ≅ p ⋙ u :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Prelocalized.functor u p)
      (Functor.Pushforward.projection.comparisonIso u p h_inverts) ≪≫
    Prelocalized.projectionIso u p

/-- The pushforward unit as a pseudo-slice morphism over `D`, formed from an explicit proof that
the source projection inverts the pushforward fractions. -/
@[stacks 04WG "explicit localized unit over morphism"]
noncomputable def over (u : C ⥤ D) (p : S ⥤ C)
    (h_inverts : (u.pushforwardFractions p).IsInvertedBy
      (Functor.Pushforward.sourceProjection u p)) :
    Functor.OverIso (p ⋙ u) (Functor.Pushforward.projection u p h_inverts) :=
  { functor := functor u p
    iso := projectionIso u p h_inverts }

/-- Relative to an explicitly induced projection, every arrow of the pushforward unit is a hom
lift over the image under `u` of its base arrow. -/
@[stacks 04WG "explicit localized unit hom lift"]
theorem functor.map.isHomLift (u : C ⥤ D) (p : S ⥤ C)
    (h_inverts : (u.pushforwardFractions p).IsInvertedBy
      (Functor.Pushforward.sourceProjection u p))
    {x y : S} (f : x ⟶ y) :
    (Functor.Pushforward.projection u p h_inverts).IsHomLift
      (u.map (p.map f)) ((functor u p).map f) := sorry

/-- Relative to an explicitly induced projection, the pushforward unit preserves strongly
cartesian arrows under the finite-limit hypotheses used to construct pushforward. -/
@[stacks 04WG "explicit localized unit strongly cartesian map"]
theorem functor.map.isStronglyCartesian (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (h_inverts : (u.pushforwardFractions p).IsInvertedBy
      (Functor.Pushforward.sourceProjection u p))
    {x y : S} (f : x ⟶ y) (hf : p.IsStronglyCartesian (p.map f) f) :
    (Functor.Pushforward.projection u p h_inverts).IsStronglyCartesian
      ((Functor.Pushforward.projection u p h_inverts).map ((functor u p).map f))
      ((functor u p).map f) := sorry

end Explicit

/-- The localized unit projection comparison formed from an explicit projection choice. -/
@[stacks 04WG "chosen localized unit projection isomorphism"]
noncomputable def projectionIso (u : C ⥤ D) (p : S ⥤ C)
    (h : Functor.Pushforward.ProjectionChoice u p) :
    functor u p ⋙ u.pushforwardProjection p h ≅ p ⋙ u :=
  Explicit.projectionIso u p h.inverts

/-- The pushforward unit as a pseudo-slice morphism over `D`, formed from an explicit projection
choice. -/
@[stacks 04WG "chosen localized unit over morphism"]
noncomputable def over (u : C ⥤ D) (p : S ⥤ C)
    (h : Functor.Pushforward.ProjectionChoice u p) :
    Functor.OverIso (p ⋙ u) (u.pushforwardProjection p h) where
  functor := functor u p
  iso := projectionIso u p h

/-- Every arrow of the explicitly based pushforward unit is a hom lift over the image under `u`
of its base arrow. -/
@[stacks 04WG "chosen localized unit hom lift"]
theorem functor.map.isHomLift (u : C ⥤ D) (p : S ⥤ C)
    (h : Functor.Pushforward.ProjectionChoice u p)
    {x y : S} (f : x ⟶ y) :
    (u.pushforwardProjection p h).IsHomLift
      (u.map (p.map f)) ((functor u p).map f) := sorry

/-- The explicitly based pushforward unit preserves strongly cartesian arrows under the
finite-limit hypotheses used to construct the fibered pushforward projection. -/
@[stacks 04WG "chosen localized unit strongly cartesian map"]
theorem functor.map.isStronglyCartesian (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (h : Functor.Pushforward.ProjectionChoice u p)
    {x y : S} (f : x ⟶ y) (hf : p.IsStronglyCartesian (p.map f) f) :
    (u.pushforwardProjection p h).IsStronglyCartesian
      ((u.pushforwardProjection p h).map ((functor u p).map f))
      ((functor u p).map f) := sorry

end Unit

end Functor.Pushforward

end CategoryTheory
