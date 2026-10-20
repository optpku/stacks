/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.ResidueFieldTrdeg
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocalAt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Residue-field transcendence degree of a morphism of algebraic spaces

The transcendence degree of a point `x` of `X` over its image under `f : X ⟶ Y`
is the étale-local residue-field invariant `trdeg` of `x/f(x)`,
computed on any étale scheme square through `x`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The transcendence degree of a point `x` of `X` over its image under a morphism
`f : X ⟶ Y` of algebraic spaces, as the supremum of scheme-level residue-field
transcendence degrees along étale scheme squares through `x`. -/
noncomputable def residueFieldTranscendenceDegreeAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) : ℕ∞ :=
  ⨆ (U : Over S) (V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (u : U.left) (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (commutes : a ≫ f = ofOverMap h ≫ b) (point_eq : Points.mapOfOver a u = x),
    Scheme.Hom.residueFieldTranscendenceDegreeAt h.left u

/-- The residue-field transcendence degree of `f` at `x` equals the scheme-level
residue-field transcendence degree of the top arrow of any étale scheme square
through `x`. -/
theorem residueFieldTranscendenceDegreeAt_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (u : U.left) {x : Points X}
    (hx : Points.mapOfOver a u = x) :
    residueFieldTranscendenceDegreeAt f x = Scheme.Hom.residueFieldTranscendenceDegreeAt h.left u :=
  sorry

/-- On a morphism of schemes over `S`, viewed as a morphism of algebraic spaces,
the residue-field transcendence degree recovers the scheme-level invariant. -/
theorem residueFieldTranscendenceDegreeAt_ofOverMap {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (u : U.left) :
    residueFieldTranscendenceDegreeAt (ofOverMap h) (ofOver.pointsEquiv U u) =
      Scheme.Hom.residueFieldTranscendenceDegreeAt h.left u :=
  sorry

/-- Residue-field transcendence degree is finite for a locally finite type morphism. -/
theorem residueFieldTranscendenceDegreeAt_lt_top {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : Points X) :
    residueFieldTranscendenceDegreeAt f x < ⊤ := sorry

/-- The finite residue-field transcendence degree of a locally finite type morphism. -/
noncomputable def residueFieldTrdegAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : Points X) : ℕ :=
  (residueFieldTranscendenceDegreeAt f x).toNat

/-- The natural-valued finite degree recovers the general extended degree. -/
theorem residueFieldTrdegAt_coe {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : Points X) :
    (residueFieldTrdegAt f x : ℕ∞) = residueFieldTranscendenceDegreeAt f x := sorry

/-- The finite degree is computed on any étale scheme square through the point. -/
theorem residueFieldTrdegAt_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {U V : Over S}
    (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (u : U.left) {x : Points X}
    (hx : Points.mapOfOver a u = x) :
    residueFieldTrdegAt f x = Scheme.Hom.residueFieldTrdegAt h.left u := sorry

/-- On a locally finite type scheme morphism the finite degree is the scheme degree. -/
theorem residueFieldTrdegAt_ofOverMap {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) [LocallyOfFiniteType (ofOverMap h)] (u : U.left) :
    residueFieldTrdegAt (ofOverMap h) (ofOver.pointsEquiv U u) =
      Scheme.Hom.residueFieldTrdegAt h.left u := sorry

namespace residueFieldTrdegAt

/-- Every point of the source of a morphism of algebraic spaces lies on an étale
scheme square over that morphism. -/
theorem exists_etaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
      (u : U.left),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b ∧
          a ≫ f = ofOverMap h ≫ b ∧ Points.mapOfOver a u = x :=
  sorry

/-- A locally quasi-finite first morphism preserves the residue-field transcendence
degree over the image under a locally finite type second morphism. -/
@[stacks 06RX]
theorem comp_eq_of_locallyQuasiFinite
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyQuasiFinite f] [LocallyOfFiniteType g] (x : Points X) :
    residueFieldTrdegAt (f ≫ g) x = residueFieldTrdegAt g (Points.map f x) :=
  sorry

end residueFieldTrdegAt

open Scheme.Germ.MorphismProperty

/-- The residue-field transcendence degree of a source point over its image
equals the prescribed extended natural number `r`. -/
def ResidueFieldTrdegEqAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (r : ℕ∞) (x : Points X) : Prop :=
  residueFieldTranscendenceDegreeAt f x = r

/-- Residue-field transcendence degree `r` at `x` is the existence of an étale
scheme square through `x` whose induced germ morphism has residue-field
transcendence degree `r`. -/
theorem residueFieldTrdegEqAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (r : ℕ∞) (x : Points X) :
    ResidueFieldTrdegEqAt f r x ↔ existsEtaleSquareAt (residueFieldTrdegEq r) f x :=
  sorry

/-- Residue-field transcendence degree `r` at `x` holds if and only if every
étale scheme square through `x` has residue-field transcendence degree `r` on
the induced germ morphism. -/
theorem residueFieldTrdegEqAt_iff_forall {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (r : ℕ∞) (x : Points X) :
    ResidueFieldTrdegEqAt f r x ↔ forallEtaleSquareAt (residueFieldTrdegEq r) f x :=
  sorry

namespace ResidueFieldTrdegEqAt

/-- An étale scheme square over `f` through `x` whose induced germ morphism has
residue-field transcendence degree `r` witnesses `ResidueFieldTrdegEqAt f r x`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {r : ℕ∞}
    {x : Points X} {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    (h : U ⟶ V) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x)
    (hr : residueFieldTrdegEq r (ofOverGermHom h u)) :
    ResidueFieldTrdegEqAt f r x :=
  sorry

/-- If the residue-field transcendence degree of `x / f(x)` is `r`, then the
induced germ morphism of any étale scheme square through `x` has residue-field
transcendence degree `r`. -/
theorem apply {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {r : ℕ∞}
    {x : Points X} (hf : ResidueFieldTrdegEqAt f r x) {U V : Over S}
    (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x) :
    residueFieldTrdegEq r (ofOverGermHom h u) :=
  sorry

end ResidueFieldTrdegEqAt

/-- Given one étale scheme square over `f` through `x`, the residue-field
transcendence degree of `x / f(x)` is `r` if and only if the induced germ
morphism has residue-field transcendence degree `r`. -/
theorem residueFieldTrdegEqAt_iff_of_etale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {r : ℕ∞} {x : Points X}
    {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x) :
    ResidueFieldTrdegEqAt f r x ↔ residueFieldTrdegEq r (ofOverGermHom h u) :=
  sorry

/-- On a morphism of schemes over `S`, viewed as a morphism of algebraic spaces,
the residue-field transcendence degree at the image of `u` is `r` if and only
if the induced germ morphism has residue-field transcendence degree `r`. -/
theorem residueFieldTrdegEqAt_ofOverMap_iff {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (r : ℕ∞) (u : U.left) :
    ResidueFieldTrdegEqAt (ofOverMap h) r (ofOver.pointsEquiv U u) ↔
      residueFieldTrdegEq r (ofOverGermHom h u) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
