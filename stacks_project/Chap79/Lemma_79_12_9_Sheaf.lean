module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Whiskering
public import stacks_project.Chap79.Lemma_79_12_2_FinitePart

/-!
# Finite-part sheaves as fppf sheaves over a base scheme

This module records the forgetful functor from algebraic spaces to universe-raised
fppf sheaves, the structure morphism `(X/Y)_fin ⟶ Y`, the fibre identification
`T ×_{Y'} X' ≅ T ×_Y X` along a space pullback square, and the induced comparison
of finite-part sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Universe-raised functor of points of an algebraic space, as an fppf sheaf. -/
theorem toFppfSheaf_isSheaf (S : Scheme.{u}) (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (X.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) :=
  sorry

/-- The functor sending an algebraic space over `S` to its universe-raised fppf sheaf
of points. -/
def toFppfSheaf (S : Scheme.{u}) :
    AlgebraicSpace S ⥤ Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) where
  obj X := ⟨X.functorOfPoints ⋙ uliftFunctor.{u + 1, u}, toFppfSheaf_isSheaf S X⟩
  map f := ObjectProperty.homMk (Functor.whiskerRight f uliftFunctor.{u + 1, u})

/-- The underlying presheaf of `(toFppfSheaf S).obj X` is the universe-raised functor of
points. -/
theorem toFppfSheaf_obj (S : Scheme.{u}) (X : AlgebraicSpace S) :
    ((toFppfSheaf S).obj X).obj = X.functorOfPoints ⋙ uliftFunctor.{u + 1, u} :=
  sorry

/-- The action of `toFppfSheaf S` on morphisms is universe-raising of the transformation of
functors of points. -/
theorem toFppfSheaf_map (S : Scheme.{u}) {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ((toFppfSheaf S).map f).hom = Functor.whiskerRight f uliftFunctor.{u + 1, u} :=
  sorry

/-- The component of the structure morphism `(X/Y)_fin ⟶ Y` on a scheme `T` over `S`,
sending a pair `(a, Z)` to the universe-raised `Y`-section `Point.a_elem`. -/
def finitePartToApp {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ) (p : FinitePart.Point f T.unop) :
    ((toFppfSheaf S).obj Y).obj.obj T :=
  ULift.up p.a_elem

/-- The structure morphism `(X/Y)_fin ⟶ Y` of finite-part sheaves, sending a pair
`(a, Z)` to the morphism `a : T ⟶ Y`. -/
def finitePartTo {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    finitePartSheaf f ⟶ (toFppfSheaf S).obj Y :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom (finitePartToApp f T)
      naturality := sorry }

/-- Components of `finitePartTo` are `finitePartToApp`. -/
theorem finitePartTo_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ) :
    (finitePartTo f).hom.app T = TypeCat.ofHom (finitePartToApp f T) :=
  sorry

/-- On a pair `(a, Z)`, the structure morphism records `a` as the universe-raised
section `Point.a_elem`. -/
theorem finitePartTo_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {T : Over S} (p : FinitePart.Point f T) :
    (finitePartTo f).hom.app (op T) p = ULift.up p.a_elem :=
  sorry

/-- Transport an open subspace along an isomorphism of ambient algebraic spaces,
keeping the same underlying space and postcomposing the inclusion. -/
def OpenSubspace.mapIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (e : X ≅ Y)
    (U : OpenSubspace X) : OpenSubspace Y where
  X := U.X
  ι := U.ι ≫ e.hom
  isOpenImmersion := sorry

/-- The inclusion of `OpenSubspace.mapIso e U` is `U.ι ≫ e.hom`. -/
theorem OpenSubspace.mapIso_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S} (e : X ≅ Y)
    (U : OpenSubspace X) : (OpenSubspace.mapIso e U).ι = U.ι ≫ e.hom :=
  sorry

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

/-- Transport a finite-part pair along a fibre product square of algebraic spaces,
sending `(a', Z')` to `(a' ≫ pY, Z)` with `Z` the open subspace of `T ×_Y X`
transported along `fiberIso`. -/
def congrIso {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T : Over S} (p : Point fX' T) :
    Point fX T where
  a := p.a ≫ pY
  Z := (OpenSubspace.mapIso (fiberIso h p.a) p.subspace).pointsOpens
  isFinite := sorry

/-- `congrIso` postcomposes the morphism to the base with `pY`. -/
theorem congrIso_a {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) {T : Over S} (p : Point fX' T) :
    (congrIso h p).a = p.a ≫ pY :=
  sorry

end FinitePart.Point

/-- The comparison of finite-part sheaves induced by a fibre product square of
algebraic spaces over `S`. -/
def finitePartMap {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) :
    finitePartSheaf fX' ⟶ finitePartSheaf fX :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun (p : FinitePart.Point fX' T.unop) ↦
        FinitePart.Point.congrIso h p
      naturality := sorry }

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

end AlgebraicGeometry.AlgebraicSpace
