/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Restriction of scalars for algebraic spaces

Given morphisms `X ⟶ Z ⟶ B` of algebraic spaces over a scheme `S`, the
restriction-of-scalars functor `Res_{Z/B}(X)` sends a scheme `T` over `S` to
the set of pairs `(a, b)` with `a : T ⟶ B` and `b : T ×_{a,B} Z ⟶ X` a
morphism over `Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

/-- The fibre product `T ×_{a,B} Z` of a morphism `a : T ⟶ B` from a scheme
over `S` with `g : Z ⟶ B`. -/
def fiber {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B) {T : Over S}
    (a : ofOver T ⟶ B) : AlgebraicSpace S :=
  AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackOver a g B.isSheaf
    B.representableDiagonal

/-- The projection `T ×_{a,B} Z ⟶ T`. -/
def fiberFst {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B) {T : Over S}
    (a : ofOver T ⟶ B) : fiber g a ⟶ ofOver T :=
  AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackOverFst a g B.isSheaf
    B.representableDiagonal

/-- The projection `T ×_{a,B} Z ⟶ Z`. -/
def fiberSnd {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B) {T : Over S}
    (a : ofOver T ⟶ B) : fiber g a ⟶ Z :=
  AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackOverSnd a g B.isSheaf
    B.representableDiagonal

/-- The functor of points of the fibre product `T ×_{a,B} Z`, as a presheaf
pullback. -/
def fiberFunctorOfPoints {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B)
    {T : Over S} (a : ofOver T ⟶ B) : (Over S)ᵒᵖ ⥤ Type u :=
  let aP : (ofOver T).functorOfPoints ⟶ B.functorOfPoints := a
  let gP : Z.functorOfPoints ⟶ B.functorOfPoints := g
  Limits.pullback aP gP

/-- The functor of points of `fiber g a` is the presheaf pullback of `a` and `g`. -/
theorem fiber_functorOfPoints {S : Scheme.{u}} {Z B : AlgebraicSpace S}
    (g : Z ⟶ B) {T : Over S} (a : ofOver T ⟶ B) :
    (fiber g a).functorOfPoints = fiberFunctorOfPoints g a := sorry

/-- The comparison `T' ×_{a',B} Z ⟶ T ×_{a,B} Z` induced by `φ : T' ⟶ T`. -/
def fiberMap {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B) {T T' : Over S}
    (φ : T' ⟶ T) (a : ofOver T ⟶ B) :
    fiber g ((CategoryTheory.yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ a) ⟶ fiber g a :=
  let a' : (ofOver T').functorOfPoints ⟶ B.functorOfPoints :=
    (CategoryTheory.yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ a
  let a₀ : (ofOver T).functorOfPoints ⟶ B.functorOfPoints := a
  let g₀ : Z.functorOfPoints ⟶ B.functorOfPoints := g
  let iT : (ofOver T').functorOfPoints ⟶ (ofOver T).functorOfPoints :=
    (CategoryTheory.yoneda.map φ : ofOver T' ⟶ ofOver T)
  let result : (fiber g ((CategoryTheory.yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ a)).functorOfPoints ⟶
      (fiber g a).functorOfPoints :=
    Limits.pullback.map a' g₀ a₀ g₀ iT (𝟙 Z.functorOfPoints) (𝟙 B.functorOfPoints)
      (Category.comp_id a') ((Category.comp_id g₀).trans (Category.id_comp g₀).symm)
  result

/-- `fiberMap` commutes with the first projections via `yoneda.map φ`. -/
theorem fiberMap_fst {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B)
    {T T' : Over S} (φ : T' ⟶ T) (a : ofOver T ⟶ B) :
    fiberMap g φ a ≫ fiberFst g a =
      fiberFst g ((CategoryTheory.yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ a) ≫
        (CategoryTheory.yoneda.map φ : ofOver T' ⟶ ofOver T) := sorry

/-- `fiberMap` commutes with the second projections to `Z`. -/
theorem fiberMap_snd {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B)
    {T T' : Over S} (φ : T' ⟶ T) (a : ofOver T ⟶ B) :
    fiberMap g φ a ≫ fiberSnd g a =
      fiberSnd g ((CategoryTheory.yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ a) := sorry

/-- A pair `(a, b)` consisting of a morphism `a : T ⟶ B` and a morphism
`b : T ×_{a,B} Z ⟶ X` over `Z`. -/
structure Pair {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) (T : Over S) where
  /-- The morphism `a : T ⟶ B`. -/
  base : ofOver T ⟶ B
  /-- The morphism `b : T ×_{a,B} Z ⟶ X`. -/
  lift : fiber g base ⟶ X
  /-- The morphism `b` lies over `Z`. -/
  overZ : lift ≫ f = fiberSnd g base

namespace Pair

/-- Build a restriction-of-scalars pair from a morphism `a : T ⟶ B`, a morphism
`b : T ×_{a,B} Z ⟶ X`, and the over-`Z` triangle. -/
def of {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    {T : Over S} (base : ofOver T ⟶ B) (lift : fiber g base ⟶ X)
    (overZ : lift ≫ f = fiberSnd g base) : Pair f g T where
  base := base
  lift := lift
  overZ := overZ

/-- A restriction-of-scalars pair consists of the over-`Z` triangle together with
the pullback cone identity on `T ×_{a,B} Z`. -/
theorem spec {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    {T : Over S} (p : Pair f g T) :
    p.lift ≫ f = fiberSnd g p.base ∧
      fiberFst g p.base ≫ p.base = fiberSnd g p.base ≫ g := sorry

/-- Two restriction-of-scalars pairs are equal if their base morphisms agree and
the lifts agree after transport. -/
theorem ext {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    {T : Over S} {p q : Pair f g T} (h_base : p.base = q.base)
    (h_lift : h_base ▸ p.lift = q.lift) : p = q := sorry

/-- Base change of a pair `(a, b)` along `φ : T' ⟶ T`, sending `a` to
`yoneda.map φ ≫ a` and `b` to the composite `(φ × id_Z) ≫ b`. -/
def precomp {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    {T T' : Over S} (φ : T' ⟶ T) (p : Pair f g T) : Pair f g T' :=
  let base : ofOver T' ⟶ ofOver T := CategoryTheory.yoneda.map φ
  Pair.of (base ≫ p.base) (fiberMap g φ p.base ≫ p.lift) sorry

/-- The base morphism of `precomp φ p` is `yoneda.map φ ≫ p.base`. -/
theorem precomp_base {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z}
    {g : Z ⟶ B} {T T' : Over S} (φ : T' ⟶ T) (p : Pair f g T) :
    (precomp φ p).base = (CategoryTheory.yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ p.base := sorry

/-- The lift of `precomp φ p` is `fiberMap g φ p.base ≫ p.lift`. -/
theorem precomp_lift {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z}
    {g : Z ⟶ B} {T T' : Over S} (φ : T' ⟶ T) (p : Pair f g T) :
    (precomp φ p).lift = fiberMap g φ p.base ≫ p.lift := sorry

/-- Restriction-of-scalars pairs are equivalent to dependent pairs of a base
morphism `a : T ⟶ B` and a lift over `Z`. -/
def sigmaEquiv {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z}
    {g : Z ⟶ B} {T : Over S} :
    Pair f g T ≃
      Σ (a : ofOver T ⟶ B), {b : fiber g a ⟶ X // b ≫ f = fiberSnd g a} where
  toFun p := ⟨p.base, ⟨p.lift, p.overZ⟩⟩
  invFun p := of p.fst p.snd.val p.snd.property
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- Restriction of a pair along an identity morphism leaves the pair unchanged. -/
theorem precomp_id {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z}
    {g : Z ⟶ B} {T : Over S} (p : Pair f g T) : precomp (𝟙 T) p = p := sorry

/-- Restriction along a composite morphism agrees with successive restriction. -/
theorem precomp_comp {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z}
    {g : Z ⟶ B} {T T' T'' : Over S} (φ : T'' ⟶ T') (ψ : T' ⟶ T)
    (p : Pair f g T) : precomp (φ ≫ ψ) p = precomp φ (precomp ψ p) := sorry

end Pair

end AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

namespace AlgebraicGeometry.AlgebraicSpace

/-- The restriction-of-scalars functor `Res_{Z/B}(X)`, sending a scheme `T` over
`S` to the type of pairs `(a, b)` with `a : T ⟶ B` and `b : T ×_{a,B} Z ⟶ X`
over `Z`. -/
def restrictionOfScalars {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := RestrictionOfScalars.Pair f g T.unop
  map φ := TypeCat.ofHom (RestrictionOfScalars.Pair.precomp φ.unop)
  map_id := by
    intro T
    ext p
    exact RestrictionOfScalars.Pair.precomp_id p
  map_comp := by
    intro T₁ T₂ T₃ φ ψ
    ext p
    exact RestrictionOfScalars.Pair.precomp_comp ψ.unop φ.unop p

/-- The value of `restrictionOfScalars f g` at a scheme `T` over `S` is the type
of restriction-of-scalars pairs. -/
theorem restrictionOfScalars_obj {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) (T : Over S) :
    (restrictionOfScalars f g).obj (op T) = RestrictionOfScalars.Pair f g T :=
  sorry

/-- Restriction of `restrictionOfScalars f g` along `φ : T' ⟶ T` is
`Pair.precomp φ`. -/
theorem restrictionOfScalars_map {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) {T T' : Over S} (φ : T' ⟶ T) :
    (restrictionOfScalars f g).map φ.op =
      TypeCat.ofHom (RestrictionOfScalars.Pair.precomp φ) := sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

/-- The projection `Res_{Z/B}(X) ⟶ B` sending a pair `(a, b)` to the `B`-point
`a`. -/
def toFunctorOfPoints {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) :
    restrictionOfScalars f g ⟶ B.functorOfPoints ⋙ uliftFunctor.{u + 1, u} where
  app T := TypeCat.ofHom fun p ↦ ULift.up (yonedaEquiv p.base)
  naturality := sorry

/-- The component of `toFunctorOfPoints` at `T` sends a pair to the universe-lift
of the Yoneda equivalent of its base morphism. -/
theorem toFunctorOfPoints_app {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) (T : (Over S)ᵒᵖ)
    (p : Pair f g T.unop) :
    (toFunctorOfPoints f g).app T p = ULift.up (yonedaEquiv p.base) := sorry

end AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
