/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Equivalence
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Hom.Computations
public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Forgetful
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Restriction
public import ReasLib.CategoryTheory.Fibered.Groupoids.BaseProjection.Naturality

/-!
# Functoriality of finite Hilbert stacks along a 2-commutative square

A 2-commutative square of categories fibred in groupoids induces a 1-morphism
of finite Hilbert stacks by applying the fibre functors of the horizontal maps
and composing the comparison isomorphism with the given 2-cell.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}

variable {X' X Y' Y : GroupoidsOver S}

/-- The comparison isomorphism `γ ⋆ H(α')` of the induced object, obtained by
restricting `H`, applying `H` to `α'`, identifying composite fibre functors, and
inserting the fibre of `γ`. -/
def mapSquareIso (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} (ξ : Obj F' d) :
    restrictObj ((fiberFunctor H ξ.U).obj ξ.y) ξ.π ≅
      (fiberFunctor F ξ.Z).obj ((fiberFunctor G ξ.Z).obj ξ.x) :=
  (fiberFunctor_restrictObj H ξ.y ξ.π).symm ≪≫
    (fiberFunctor H ξ.Z).mapIso ξ.iso ≪≫
    (eqToIso (congrArg (fun K ↦ K.obj ξ.x) (fiberFunctor.comp F' H ξ.Z))).symm ≪≫
    (BasedNatIso.fiber (toBasedFunctorIso γ) ξ.Z).app ξ.x ≪≫
    eqToIso (congrArg (fun K ↦ K.obj ξ.x) (fiberFunctor.comp G F ξ.Z))

/-- `mapSquareIso` is the displayed composite of restriction, `H(α')`, fibre-functor
composition, and the fibre of `γ`. -/
theorem mapSquareIso_eq (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} (ξ : Obj F' d) :
    mapSquareIso F' F G H γ ξ =
      (fiberFunctor_restrictObj H ξ.y ξ.π).symm ≪≫
        (fiberFunctor H ξ.Z).mapIso ξ.iso ≪≫
        (eqToIso (congrArg (fun K ↦ K.obj ξ.x) (fiberFunctor.comp F' H ξ.Z))).symm ≪≫
        (BasedNatIso.fiber (toBasedFunctorIso γ) ξ.Z).app ξ.x ≪≫
        eqToIso (congrArg (fun K ↦ K.obj ξ.x) (fiberFunctor.comp G F ξ.Z)) :=
  rfl

/-- Object part of the induced 1-morphism: copy `(U, Z, π)` and send
`(y, x, α)` to `(H(y), G(x), γ ⋆ H(α))`. -/
abbrev mapSquareObj (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} (ξ : Obj F' d) : Obj F d :=
  Obj.of ξ.U ξ.Z ξ.π ξ.finiteLocallyFree
    ((fiberFunctor H ξ.U).obj ξ.y) ((fiberFunctor G ξ.Z).obj ξ.x)
    (mapSquareIso F' F G H γ ξ)

/-- The `Y`-component of `mapSquareObj` is the fibre functor of `H` applied to `y`. -/
theorem mapSquareObj_y (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} (ξ : Obj F' d) :
    (mapSquareObj F' F G H γ ξ).y = (fiberFunctor H ξ.U).obj ξ.y :=
  rfl

/-- The `X`-component of `mapSquareObj` is the fibre functor of `G` applied to `x`. -/
theorem mapSquareObj_x (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} (ξ : Obj F' d) :
    (mapSquareObj F' F G H γ ξ).x = (fiberFunctor G ξ.Z).obj ξ.x :=
  rfl

/-- Applying the horizontal fibre functors preserves the compatibility square of finite
Hilbert morphisms. -/
theorem mapSquareHom_comm (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} {ξ ξ' : Obj F' d} (φ : Hom ξ ξ') :
    HomCompatible (ξ := mapSquareObj F' F G H γ ξ)
      (ξ' := mapSquareObj F' F G H γ ξ') φ.f φ.g φ.over_comm
      ((fiberFunctor H ξ.U).mapIso φ.b ≪≫ fiberFunctor_restrictObj H ξ'.y φ.f)
      ((fiberFunctor G ξ.Z).mapIso φ.a ≪≫ fiberFunctor_restrictObj G ξ'.x φ.g) :=
  sorry

/-- Morphism part of the induced 1-morphism: the same `(f, g)` with `b` and `a`
transported by the fibre functors of `H` and `G`. -/
def mapSquareHom (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} {ξ ξ' : Obj F' d} (φ : Hom ξ ξ') :
    Hom (mapSquareObj F' F G H γ ξ) (mapSquareObj F' F G H γ ξ') where
  f := φ.f
  g := φ.g
  over_comm := φ.over_comm
  isPullback := φ.isPullback
  b := (fiberFunctor H ξ.U).mapIso φ.b ≪≫ fiberFunctor_restrictObj H ξ'.y φ.f
  a := (fiberFunctor G ξ.Z).mapIso φ.a ≪≫ fiberFunctor_restrictObj G ξ'.x φ.g
  comm := mapSquareHom_comm F' F G H γ φ

/-- `mapSquareHom` preserves the underlying map of test schemes. -/
theorem mapSquareHom_f (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} {ξ ξ' : Obj F' d} (φ : Hom ξ ξ') :
    (mapSquareHom F' F G H γ φ).f = φ.f :=
  rfl

/-- `mapSquareHom` preserves the underlying map of finite locally free schemes. -/
theorem mapSquareHom_g (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} {ξ ξ' : Obj F' d} (φ : Hom ξ ξ') :
    (mapSquareHom F' F G H γ φ).g = φ.g :=
  rfl

/-- The `b`-component of `mapSquareHom` is the fibre functor of `H` applied to `b`. -/
theorem mapSquareHom_b (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} {ξ ξ' : Obj F' d} (φ : Hom ξ ξ') :
    (mapSquareHom F' F G H γ φ).b =
      (fiberFunctor H ξ.U).mapIso φ.b ≪≫ fiberFunctor_restrictObj H ξ'.y φ.f :=
  rfl

/-- The `a`-component of `mapSquareHom` is the fibre functor of `G` applied to `a`. -/
theorem mapSquareHom_a (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) {d : ℕ} {ξ ξ' : Obj F' d} (φ : Hom ξ ξ') :
    (mapSquareHom F' F G H γ φ).a =
      (fiberFunctor G ξ.Z).mapIso φ.a ≪≫ fiberFunctor_restrictObj G ξ'.x φ.g :=
  rfl

/-- The square-induced morphism operation preserves identity morphisms. -/
theorem mapSquareHom_id (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) (ξ : Obj F' d) :
    mapSquareHom F' F G H γ (𝟙 ξ) = 𝟙 (mapSquareObj F' F G H γ ξ) :=
  sorry

/-- The square-induced morphism operation preserves composition. -/
theorem mapSquareHom_comp (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) {ξ ξ' ξ'' : Obj F' d}
    (φ : ξ ⟶ ξ') (ψ : ξ' ⟶ ξ'') :
    mapSquareHom F' F G H γ (φ ≫ ψ) =
      CategoryStruct.comp (obj := Obj F d)
        (mapSquareHom F' F G H γ φ) (mapSquareHom F' F G H γ ψ) :=
  sorry

/-- The total functor of the induced 1-morphism `H_d(X'/Y') ⟶ H_d(X/Y)`. -/
def mapSquareFunctor (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    Obj F' d ⥤ Obj F d where
  obj ξ := mapSquareObj F' F G H γ ξ
  map φ := mapSquareHom F' F G H γ φ
  map_id := mapSquareHom_id F' F G H γ d
  map_comp := mapSquareHom_comp F' F G H γ d

/-- `mapSquareFunctor` lies strictly over the identity on test schemes. -/
theorem mapSquareFunctor_w (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    mapSquareFunctor F' F G H γ d ⋙ p F d = p F' d :=
  rfl

/-- The image of a quintuple under `mapSquareFunctor` is `mapSquareObj`. -/
theorem mapSquare_obj (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) (ξ : Obj F' d) :
    (mapSquareFunctor F' F G H γ d).obj ξ = mapSquareObj F' F G H γ ξ :=
  rfl

/-- `mapSquareFunctor` preserves the underlying test scheme. -/
theorem mapSquare_U (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) (ξ : Obj F' d) :
    ((mapSquareFunctor F' F G H γ d).obj ξ).U = ξ.U :=
  rfl

/-- `mapSquareFunctor` preserves the finite locally free scheme. -/
theorem mapSquare_Z (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) (ξ : Obj F' d) :
    ((mapSquareFunctor F' F G H γ d).obj ξ).Z = ξ.Z :=
  rfl

/-- The `Y`-component of the image is `H(y)`. -/
theorem mapSquare_y (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) (ξ : Obj F' d) :
    ((mapSquareFunctor F' F G H γ d).obj ξ).y = (fiberFunctor H ξ.U).obj ξ.y :=
  rfl

/-- The `X`-component of the image is `G(x)`. -/
theorem mapSquare_x (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) (ξ : Obj F' d) :
    ((mapSquareFunctor F' F G H γ d).obj ξ).x = (fiberFunctor G ξ.Z).obj ξ.x :=
  rfl

/-- The comparison isomorphism of the image is `mapSquareIso`. -/
theorem mapSquare_iso (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) (ξ : Obj F' d) :
    ((mapSquareFunctor F' F G H γ d).obj ξ).iso = mapSquareIso F' F G H γ ξ :=
  rfl

/-- The based functor of the induced 1-morphism of finite Hilbert stacks. -/
def mapSquareBased (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X) (H : Y' ⟶ Y)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    BasedCategory.ofFunctor (p F' d) ⥤ᵇ BasedCategory.ofFunctor (p F d) :=
  BasedFunctor.ofFunctor (mapSquareFunctor F' F G H γ d)
    (mapSquareFunctor_w F' F G H γ d)

/-- Forgetting `mapSquareBased` to total functors recovers `mapSquareFunctor`. -/
theorem mapSquareBased_toFunctor (F' : X' ⟶ Y') (F : X ⟶ Y) (G : X' ⟶ X)
    (H : Y' ⟶ Y) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    (mapSquareBased F' F G H γ d).toFunctor = mapSquareFunctor F' F G H γ d :=
  rfl

/-- The inverse base-projection naturality isomorphism, adjusted by the right unitor,
compares structure morphisms to `S`. -/
private def schemeProjectionCell {X' X : GroupoidsOver S} (G : X' ⟶ X) :
    baseProjection.{u + 1, u, u + 1} X' ≫ 𝟙 (schemeBase S) ≅
      G ≫ baseProjection.{u + 1, u, u + 1} X :=
  (ρ_ (baseProjection.{u + 1, u, u + 1} X')).symm ≪≫ (baseProjection.naturality G).symm

variable {𝒳' 𝒳 𝒴' 𝒴 :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

open StackOver.Groupoids.Hom

/-- Transport a 2-isomorphism of stack morphisms to the underlying groupoid-fibred
square `F' ≫ H ≅ G ≫ F`. -/
def mapSquareCell (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴)
    (γ : F' ≫ H ≅ G ≫ F) :
    toGroupoidsMor F' ≫ toGroupoidsMor H ≅ toGroupoidsMor G ≫ toGroupoidsMor F :=
  eqToIso (toGroupoidsMor.comp F' H).symm ≪≫
    toGroupoidsMorIso γ ≪≫ eqToIso (toGroupoidsMor.comp G F)

/-- `mapSquareCell` is `toGroupoidsMorIso γ` after the composition identifications. -/
theorem mapSquareCell_eq (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴)
    (γ : F' ≫ H ≅ G ≫ F) :
    mapSquareCell F' F G H γ =
      eqToIso (toGroupoidsMor.comp F' H).symm ≪≫
        toGroupoidsMorIso γ ≪≫ eqToIso (toGroupoidsMor.comp G F) :=
  rfl

/-- The 1-morphism `H_d(𝒳') ⟶ H_d(𝒳)` induced by `G` along structure morphisms to
`S`. -/
def mapSquareAbsolute (G : 𝒳' ⟶ 𝒳) (d : ℕ) :
    ofStack 𝒳'.toGroupoids d ⟶ ofStack 𝒳.toGroupoids d :=
  lift (ofBasedFunctor (mapSquareBased (toSchemeProjection 𝒳') (toSchemeProjection 𝒳)
    (toGroupoidsMor G) (𝟙 (schemeBase S)) (schemeProjectionCell (toGroupoidsMor G)) d))

/-- Forgetting `mapSquareAbsolute` to based functors recovers `mapSquareBased` of
the structure-morphism square. -/
theorem mapSquareAbsolute_toBasedFunctor (G : 𝒳' ⟶ 𝒳) (d : ℕ) :
    toBasedFunctor (mapSquareAbsolute G d) =
      mapSquareBased (toSchemeProjection 𝒳') (toSchemeProjection 𝒳)
        (toGroupoidsMor G) (𝟙 (schemeBase S))
        (schemeProjectionCell (toGroupoidsMor G)) d :=
  rfl

end AlgebraicGeometry.FiniteHilbertStack

namespace AlgebraicGeometry

open FiniteHilbertStack StackOver.Groupoids.Hom

variable {S : Scheme.{u}}
variable {𝒳' 𝒳 𝒴' 𝒴 :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- The 1-morphism `H_d(𝒳'/𝒴') ⟶ H_d(𝒳/𝒴)` of stacks in groupoids induced by a
2-commutative square. -/
def finiteHilbertMapSquare (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴)
    (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    stack (toGroupoidsMor F') d ⟶ stack (toGroupoidsMor F) d :=
  lift (ofBasedFunctor (mapSquareBased (toGroupoidsMor F') (toGroupoidsMor F)
    (toGroupoidsMor G) (toGroupoidsMor H) (mapSquareCell F' F G H γ) d))

/-- Forgetting `finiteHilbertMapSquare` to based functors recovers `mapSquareBased` of the
underlying groupoid-fibred square. -/
theorem finiteHilbertMapSquare_toBasedFunctor (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
    (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    toBasedFunctor (finiteHilbertMapSquare F' F G H γ d) =
      mapSquareBased (toGroupoidsMor F') (toGroupoidsMor F) (toGroupoidsMor G)
        (toGroupoidsMor H) (mapSquareCell F' F G H γ) d :=
  rfl

/-- The square-induced morphism commutes with forgetting all stack-valued data. -/
theorem finiteHilbertMapSquare_comp_forgetToPoint (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    finiteHilbertMapSquare F' F G H γ d ≫ forgetToPoint F d =
      forgetToPoint F' d :=
  sorry

/-- The square-induced morphism commutes with forgetting the target fibre object and its comparison. -/
theorem finiteHilbertMapSquare_comp_forgetToAbsolute (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    finiteHilbertMapSquare F' F G H γ d ≫ forgetToAbsolute F d =
      forgetToAbsolute F' d ≫ mapSquareAbsolute G d :=
  sorry

/-- The square-induced morphism commutes with the projection to the target stack. -/
theorem finiteHilbertMapSquare_comp_forgetToY (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) :
    finiteHilbertMapSquare F' F G H γ d ≫ forgetToY F d =
      forgetToY F' d ≫ H :=
  sorry

end AlgebraicGeometry
