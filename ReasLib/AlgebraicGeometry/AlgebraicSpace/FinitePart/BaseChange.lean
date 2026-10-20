/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Iso
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Base change of finite-part sheaves -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The identification `T ×_{Y'} X' ≅ T ×_Y X` induced by a fibre product square of
algebraic spaces over `S`. -/
def fiberIso {S : Scheme.{u}} {X X' Y Y' T : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) (a' : T ⟶ Y') :
    pullback a' fX' ≅ pullback (a' ≫ pY) fX :=
  ((IsPullback.of_hasPullback a' fX').flip.paste_horiz h).flip.isoPullback

/-- The first projection of `fiberIso h a'` recovers `pullback.fst a' fX'`. -/
theorem fiberIso_hom_fst {S : Scheme.{u}} {X X' Y Y' T : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) (a' : T ⟶ Y') :
    (fiberIso h a').hom ≫ pullback.fst (a' ≫ pY) fX = pullback.fst a' fX' :=
  sorry

/-- The second projection of `fiberIso h a'` recovers `pullback.snd a' fX' ≫ pX`. -/
theorem fiberIso_hom_snd {S : Scheme.{u}} {X X' Y Y' T : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) (a' : T ⟶ Y') :
    (fiberIso h a').hom ≫ pullback.snd (a' ≫ pY) fX = pullback.snd a' fX' ≫ pX :=
  sorry

namespace FinitePart.Point

/-- The open reconstructed from the transported points-open is finite over the test scheme. -/
theorem congrIso_isFinite {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T : Over S} (p : Point fX' T) :
    IsFinite
      ((OpenSubspace.fromOpens
        (OpenSubspace.mapIso (fiberIso h p.a) p.subspace).pointsOpens).ι ≫
          pullback.fst (p.a ≫ pY) fX) :=
  sorry

/-- Transport a finite-part pair along a fibre product square of algebraic spaces,
sending `(a', Z')` to `(a' ≫ pY, Z)` with `Z` the open subspace of `T ×_Y X`
transported along `fiberIso`. -/
def congrIso {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T : Over S} (p : Point fX' T) :
    Point fX T where
  a := p.a ≫ pY
  Z := (OpenSubspace.mapIso (fiberIso h p.a) p.subspace).pointsOpens
  isFinite := congrIso_isFinite h p

/-- `congrIso` postcomposes the morphism to the base with `pY`. -/
theorem congrIso_a {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T : Over S} (p : Point fX' T) :
    (congrIso h p).a = p.a ≫ pY :=
  sorry

end FinitePart.Point

/-- Transport of finite-part pairs along a pullback square commutes with restriction. -/
theorem finitePartMap_naturality {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T T' : (Over S)ᵒᵖ} (g : T ⟶ T') :
    (finitePartSheaf fX').obj.map g ≫
        TypeCat.ofHom (fun (p : FinitePart.Point fX' T'.unop) ↦
          FinitePart.Point.congrIso h p) =
      TypeCat.ofHom (fun (p : FinitePart.Point fX' T.unop) ↦
        FinitePart.Point.congrIso h p) ≫ (finitePartSheaf fX).obj.map g :=
  sorry

/-- The comparison of finite-part sheaves induced by a fibre product square of
algebraic spaces over `S`. -/
def finitePartMap {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) :
    finitePartSheaf fX' ⟶ finitePartSheaf fX :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun (p : FinitePart.Point fX' T.unop) ↦
        FinitePart.Point.congrIso h p
      naturality := fun _ _ g ↦ finitePartMap_naturality h g }

/-- Components of `finitePartMap h` are `FinitePart.Point.congrIso h`. -/
theorem finitePartMap_app {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) (T : (Over S)ᵒᵖ) :
    (finitePartMap h).hom.app T =
      TypeCat.ofHom fun (p : FinitePart.Point fX' T.unop) ↦ FinitePart.Point.congrIso h p :=
  sorry

/-- On a pair `(a', Z')` over `T`, `finitePartMap h` postcomposes `a'` with `pY`. -/
theorem finitePartMap_a {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T : Over S} (p : FinitePart.Point fX' T) :
    ((finitePartMap h).hom.app (op T) p).a = p.a ≫ pY :=
  sorry

/-- On a pair `(a', Z')` over `T`, `finitePartMap h` is `FinitePart.Point.congrIso h`. -/
theorem finitePartMap_spec {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T : Over S} (p : FinitePart.Point fX' T) :
    (finitePartMap h).hom.app (op T) p = FinitePart.Point.congrIso h p :=
  sorry

/-- The comparison `finitePartMap h` commutes with the structure morphisms to `Y'` and
`Y`. -/
theorem finitePartMap_comm {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) :
    finitePartMap h ≫ finitePartTo fX = finitePartTo fX' ≫ (toFppfSheaf S).map pY :=
  sorry

/-- On a scheme `T` over `S`, the finite-part sheaf square is a fibre product of
types. -/
theorem finitePart_isPullback_app {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) (T : (Over S)ᵒᵖ) :
    IsPullback ((finitePartMap h).hom.app T) ((finitePartTo fX').hom.app T)
      ((finitePartTo fX).hom.app T) (((toFppfSheaf S).map pY).hom.app T) :=
  sorry

/-- Finite-part sheaves commute with arbitrary base change of algebraic spaces. -/
theorem finitePart_isPullback {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) :
    IsPullback (finitePartMap h) (finitePartTo fX') (finitePartTo fX)
      ((toFppfSheaf S).map pY) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
