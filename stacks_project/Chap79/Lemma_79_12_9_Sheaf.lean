/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.BaseChange
public import stacks_project.Chap79.Lemma_79_12_2_FinitePart

/-! # Finite-part sheaves and their base-change comparison -/

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite TypeCat

universe u

#check (AlgebraicGeometry.AlgebraicSpace.toFppfSheaf_isSheaf :
  ∀ (S : Scheme.{u}) (X : AlgebraicSpace S),
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (X.functorOfPoints ⋙ uliftFunctor.{u + 1, u}))

#check (AlgebraicGeometry.AlgebraicSpace.toFppfSheaf :
  ∀ (S : Scheme.{u}),
    AlgebraicSpace S ⥤ Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))

#check (AlgebraicGeometry.AlgebraicSpace.toFppfSheaf_obj :
  ∀ (S : Scheme.{u}) (X : AlgebraicSpace S),
    ((toFppfSheaf S).obj X).obj = X.functorOfPoints ⋙ uliftFunctor.{u + 1, u})

#check (AlgebraicGeometry.AlgebraicSpace.toFppfSheaf_map :
  ∀ (S : Scheme.{u}) {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    ((toFppfSheaf S).map f).hom = Functor.whiskerRight f uliftFunctor.{u + 1, u})

#check (AlgebraicGeometry.AlgebraicSpace.finitePartToApp :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ) (p : FinitePart.Point f T.unop),
    ((toFppfSheaf S).obj Y).obj.obj T)

#check (AlgebraicGeometry.AlgebraicSpace.finitePartTo :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    finitePartSheaf f ⟶ (toFppfSheaf S).obj Y)

#check (AlgebraicGeometry.AlgebraicSpace.finitePartTo_app :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ),
    (finitePartTo f).hom.app T = TypeCat.ofHom (finitePartToApp f T))

#check (AlgebraicGeometry.AlgebraicSpace.finitePartTo_spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {T : Over S} (p : FinitePart.Point f T),
    (finitePartTo f).hom.app (op T) p = ULift.up p.a_elem)

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.mapIso :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (e : X ≅ Y)
    (U : OpenSubspace X),
    OpenSubspace Y)

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.mapIso_ι :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (e : X ≅ Y)
    (U : OpenSubspace X),
    (OpenSubspace.mapIso e U).ι = U.ι ≫ e.hom)

#check (AlgebraicGeometry.AlgebraicSpace.fiberIso :
  ∀ {S : Scheme.{u}} {X X' Y Y' T : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) (a' : T ⟶ Y'),
    pullback a' fX' ≅ pullback (a' ≫ pY) fX)

#check (AlgebraicGeometry.AlgebraicSpace.fiberIso_hom_fst :
  ∀ {S : Scheme.{u}} {X X' Y Y' T : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) (a' : T ⟶ Y'),
    (fiberIso h a').hom ≫ pullback.fst (a' ≫ pY) fX = pullback.fst a' fX')

#check (AlgebraicGeometry.AlgebraicSpace.fiberIso_hom_snd :
  ∀ {S : Scheme.{u}} {X X' Y Y' T : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) (a' : T ⟶ Y'),
    (fiberIso h a').hom ≫ pullback.snd (a' ≫ pY) fX = pullback.snd a' fX' ≫ pX)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.congrIso :
  ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T : Over S} (p : FinitePart.Point fX' T),
    FinitePart.Point fX T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.Point.congrIso_a :
  ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T : Over S} (p : FinitePart.Point fX' T),
    (FinitePart.Point.congrIso h p).a = p.a ≫ pY)

#check (AlgebraicGeometry.AlgebraicSpace.finitePartMap :
  ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY),
    finitePartSheaf fX' ⟶ finitePartSheaf fX)

#check (AlgebraicGeometry.AlgebraicSpace.finitePartMap_app :
  ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) (T : (Over S)ᵒᵖ),
    (finitePartMap h).hom.app T =
      TypeCat.ofHom fun (p : FinitePart.Point fX' T.unop) ↦ FinitePart.Point.congrIso h p)

#check (AlgebraicGeometry.AlgebraicSpace.finitePartMap_a :
  ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T : Over S} (p : FinitePart.Point fX' T),
    ((finitePartMap h).hom.app (op T) p).a = p.a ≫ pY)

#check (AlgebraicGeometry.AlgebraicSpace.finitePartMap_spec :
  ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T : Over S} (p : FinitePart.Point fX' T),
    (finitePartMap h).hom.app (op T) p = FinitePart.Point.congrIso h p)

#check (AlgebraicGeometry.AlgebraicSpace.finitePartMap_comm :
  ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY),
    finitePartMap h ≫ finitePartTo fX = finitePartTo fX' ≫ (toFppfSheaf S).map pY)

#check (AlgebraicGeometry.AlgebraicSpace.finitePart_isPullback_app :
  ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) (T : (Over S)ᵒᵖ),
    IsPullback ((finitePartMap h).hom.app T) ((finitePartTo fX').hom.app T)
      ((finitePartTo fX).hom.app T) (((toFppfSheaf S).map pY).hom.app T))
