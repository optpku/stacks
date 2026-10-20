module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper
public import ReasLib.AlgebraicGeometry.Polarized

/-!
# Forgetful functor from Polarized to Spaces'_{fp, flat, proper}

A polarized pair `(X ⟶ S, L)` forgets the line bundle and is viewed as an
algebraic-space family over the terminal scheme, landing in the primed
category `Spaces'_{fp, flat, proper}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.Spaces hiding p

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- Schemes as objects of `Over (⊤_ Scheme)`, via the unique map to the
terminal scheme. -/
def asOverTerminal : Scheme.{u} ⥤ Over (⊤_ Scheme.{u}) where
  obj X := X.asOver (⊤_ Scheme.{u})
  map f := f.asOver (⊤_ Scheme.{u})
  map_id := sorry
  map_comp := sorry

/-- The object map of `asOverTerminal` is `Scheme.asOver` of the terminal
scheme. -/
theorem asOverTerminal_obj (X : Scheme.{u}) :
    asOverTerminal.obj X = X.asOver (⊤_ Scheme.{u}) :=
  sorry

/-- The morphism map of `asOverTerminal` is `Scheme.Hom.asOver` of the terminal
scheme. -/
theorem asOverTerminal_map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    asOverTerminal.map f = f.asOver (⊤_ Scheme.{u}) :=
  sorry

/-- The algebraic-space family of a polarized object, obtained by viewing the
structure morphism as a morphism of algebraic spaces over the terminal
scheme. -/
def toHom (x : Obj) :
    ofOver (x.X.asOver (⊤_ Scheme.{u})) ⟶ ofOver (x.S.asOver (⊤_ Scheme.{u})) :=
  (ofOverFunctor (⊤_ Scheme.{u})).map (x.hom.asOver (⊤_ Scheme.{u}))

/-- `toHom x` is the image of the structure morphism under `ofOverFunctor`. -/
theorem toHom_eq (x : Obj) :
    toHom x =
      (ofOverFunctor (⊤_ Scheme.{u})).map (x.hom.asOver (⊤_ Scheme.{u})) :=
  sorry

/-- The underlying algebraic-space family of a polarized object is of finite
presentation, flat, and proper. -/
instance toHom_fpFlatProper (x : Obj) : FpFlatProper (toHom x) :=
  sorry

/-- The morphism of `Spaces` obtained by forgetting the line bundle of a
polarized morphism. -/
def toSpacesHom {x y : Obj} (φ : x ⟶ y) :
    Spaces.mk (toHom x) ⟶ Spaces.mk (toHom y) where
  left := (ofOverFunctor (⊤_ Scheme.{u})).map (φ.map.asOver (⊤_ Scheme.{u}))
  right := φ.base.asOver (⊤_ Scheme.{u})
  w := sorry

/-- The left component of `toSpacesHom φ` is the algebraic-space map of `φ.map`. -/
theorem toSpacesHom_left {x y : Obj} (φ : x ⟶ y) :
    (toSpacesHom φ).left =
      (ofOverFunctor (⊤_ Scheme.{u})).map (φ.map.asOver (⊤_ Scheme.{u})) :=
  sorry

/-- The right component of `toSpacesHom φ` is `φ.base` over the terminal scheme. -/
theorem toSpacesHom_right {x y : Obj} (φ : x ⟶ y) :
    (toSpacesHom φ).right = φ.base.asOver (⊤_ Scheme.{u}) :=
  sorry

/-- The morphism of `FtGroupoids` obtained by forgetting the line bundle of a
polarized morphism. -/
def toFtGroupoidsHom {x y : Obj} (φ : x ⟶ y) :
    FtGroupoids.mk (toHom x) ⟶ FtGroupoids.mk (toHom y) where
  hom := { hom := toSpacesHom φ }
  property := sorry

/-- The underlying `Spaces` morphism of `toFtGroupoidsHom φ` is `toSpacesHom φ`. -/
theorem toFtGroupoidsHom_hom {x y : Obj} (φ : x ⟶ y) :
    (toFtGroupoidsHom φ).hom.hom = toSpacesHom φ :=
  sorry

/-- The morphism of `FpFlatProperGroupoids` obtained by forgetting the line
bundle of a polarized morphism. -/
def toFpFlatProperHom {x y : Obj} (φ : x ⟶ y) :
    FpFlatProperGroupoids.mk (toHom x) ⟶ FpFlatProperGroupoids.mk (toHom y) where
  hom := toFtGroupoidsHom φ

/-- The underlying `FtGroupoids` morphism of `toFpFlatProperHom φ` is
`toFtGroupoidsHom φ`. -/
theorem toFpFlatProperHom_hom {x y : Obj} (φ : x ⟶ y) :
    (toFpFlatProperHom φ).hom = toFtGroupoidsHom φ :=
  sorry

/-- The forgetful functor `Polarized ⥤ Spaces'_{fp, flat, proper}` sending
`(X ⟶ S, L)` to the algebraic-space family `X ⟶ S` over the terminal scheme. -/
def toFpFlatProper : Obj ⥤ FpFlatProperGroupoids (⊤_ Scheme.{u}) where
  obj x := FpFlatProperGroupoids.mk (toHom x)
  map φ := toFpFlatProperHom φ
  map_id := sorry
  map_comp := sorry

/-- The object map of `toFpFlatProper` is `FpFlatProperGroupoids.mk` of `toHom`. -/
theorem toFpFlatProper_obj (x : Obj) :
    toFpFlatProper.obj x = FpFlatProperGroupoids.mk (toHom x) :=
  sorry

/-- The morphism map of `toFpFlatProper` is `toFpFlatProperHom`. -/
theorem toFpFlatProper_map {x y : Obj} (φ : x ⟶ y) :
    toFpFlatProper.map φ = toFpFlatProperHom φ :=
  sorry

/-- Forgetting the line bundle and then projecting to `Over (⊤_ Scheme)` recovers
the base-scheme functor of Polarized, after identifying schemes with objects of
`Over (⊤_ Scheme)`. -/
theorem toFpFlatProper_comp_p :
    toFpFlatProper ⋙ pFpFlatProperGroupoids (⊤_ Scheme.{u}) = p ⋙ asOverTerminal :=
  sorry

end AlgebraicGeometry.Polarized
