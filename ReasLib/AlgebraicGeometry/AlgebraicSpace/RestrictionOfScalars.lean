/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictScalars.Pair
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf

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
  pullback a g

/-- The projection `T ×_{a,B} Z ⟶ T`. -/
def fiberFst {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B) {T : Over S}
    (a : ofOver T ⟶ B) : fiber g a ⟶ ofOver T :=
  pullback.fst a g

/-- The projection `T ×_{a,B} Z ⟶ Z`. -/
def fiberSnd {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B) {T : Over S}
    (a : ofOver T ⟶ B) : fiber g a ⟶ Z :=
  pullback.snd a g

/-- The functor of points of the fibre product `T ×_{a,B} Z`, using the canonical
categorical pullback. -/
def fiberFunctorOfPoints {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B)
    {T : Over S} (a : ofOver T ⟶ B) : (Over S)ᵒᵖ ⥤ Type u :=
  (fiber g a).functorOfPoints

/-- The functor of points of `fiber g a` is the canonical fibre presheaf. -/
theorem fiber_functorOfPoints {S : Scheme.{u}} {Z B : AlgebraicSpace S}
    (g : Z ⟶ B) {T : Over S} (a : ofOver T ⟶ B) :
    (fiber g a).functorOfPoints = fiberFunctorOfPoints g a := rfl

/-- The comparison `T' ×_{a',B} Z ⟶ T ×_{a,B} Z` induced by `φ : T' ⟶ T`. -/
def fiberMap {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B) {T T' : Over S}
    (φ : T' ⟶ T) (a : ofOver T ⟶ B) :
    fiber g ((CategoryTheory.yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ a) ⟶ fiber g a :=
  RestrictScalars.fiberMap (S := S) (Z := Z) (B := B)
    (T := ofOver T) (T' := ofOver T') g a
    (CategoryTheory.yoneda.map φ : ofOver T' ⟶ ofOver T)

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
@[deprecated RestrictScalars.Pair (since := "2026-10-22")]
abbrev Pair {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) (T : Over S) := RestrictScalars.Pair f g (ofOver T)

namespace Pair

/-- Compatibility projection to the canonical pair base morphism. -/
abbrev base {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    {T : Over S} (p : Pair f g T) := p.a

/-- Compatibility projection to the canonical pair lift. -/
abbrev lift {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    {T : Over S} (p : Pair f g T) := p.b


/-- Build a restriction-of-scalars pair from a morphism `a : T ⟶ B`, a morphism
`b : T ×_{a,B} Z ⟶ X`, and the over-`Z` triangle. -/
def of {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    {T : Over S} (base : ofOver T ⟶ B) (lift : fiber g base ⟶ X)
    (overZ : lift ≫ f = fiberSnd g base) : Pair f g T :=
  RestrictScalars.Pair.of base lift overZ

/-- A restriction-of-scalars pair consists of the over-`Z` triangle together with
the pullback cone identity on `T ×_{a,B} Z`. -/
theorem spec {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    {T : Over S} (p : Pair f g T) :
    p.lift ≫ f = fiberSnd g p.base ∧
      fiberFst g p.base ≫ p.base = fiberSnd g p.base ≫ g :=
  RestrictScalars.Pair.spec p

/-- Two restriction-of-scalars pairs are equal if their base morphisms agree and
the lifts agree after transport. -/
theorem ext {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    {T : Over S} {p q : Pair f g T} (h_base : p.base = q.base)
    (h_lift : HEq p.lift q.lift) : p = q :=
  RestrictScalars.Pair.ext h_base h_lift

/-- Precomposition of a lift preserves its triangle over `Z`. -/
theorem precomp_overZ {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    {f : X ⟶ Z} {g : Z ⟶ B} {T T' : Over S} (φ : T' ⟶ T) (p : Pair f g T) :
    (fiberMap g φ p.base ≫ p.lift) ≫ f =
      fiberSnd g ((yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ p.base) := sorry

/-- Base change of a pair `(a, b)` along `φ : T' ⟶ T`, sending `a` to
`yoneda.map φ ≫ a` and `b` to the composite `(φ × id_Z) ≫ b`. -/
def precomp {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    {T T' : Over S} (φ : T' ⟶ T) (p : Pair f g T) : Pair f g T' :=
  RestrictScalars.Pair.map p (CategoryTheory.yoneda.map φ)

/-- The base morphism of `precomp φ p` is `yoneda.map φ ≫ p.base`. -/
theorem precomp_base {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z}
    {g : Z ⟶ B} {T T' : Over S} (φ : T' ⟶ T) (p : Pair f g T) :
    (precomp φ p).base = (CategoryTheory.yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ p.base := rfl

/-- The lift of `precomp φ p` is `fiberMap g φ p.base ≫ p.lift`. -/
theorem precomp_lift {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z}
    {g : Z ⟶ B} {T T' : Over S} (φ : T' ⟶ T) (p : Pair f g T) :
    (precomp φ p).lift = fiberMap g φ p.base ≫ p.lift := rfl

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
  rfl

/-- Restriction of `restrictionOfScalars f g` along `φ : T' ⟶ T` is
`Pair.precomp φ`. -/
theorem restrictionOfScalars_map {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) {T T' : Over S} (φ : T' ⟶ T) :
    (restrictionOfScalars f g).map φ.op =
      TypeCat.ofHom (RestrictionOfScalars.Pair.precomp φ) := rfl

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

/-- Projection to the base point commutes with restriction to test schemes. -/
theorem toFunctorOfPoints_naturality {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') :
    (restrictionOfScalars f g).map φ ≫
        TypeCat.ofHom (fun (p : Pair f g T'.unop) ↦ ULift.up (yonedaEquiv p.base)) =
      TypeCat.ofHom (fun (p : Pair f g T.unop) ↦ ULift.up (yonedaEquiv p.base)) ≫
        (B.functorOfPoints ⋙ uliftFunctor.{u + 1, u}).map φ := sorry

/-- The projection `Res_{Z/B}(X) ⟶ B` sending a pair `(a, b)` to the `B`-point
`a`. -/
def toFunctorOfPoints {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) :
    restrictionOfScalars f g ⟶ B.functorOfPoints ⋙ uliftFunctor.{u + 1, u} where
  app T := TypeCat.ofHom fun p ↦ ULift.up (yonedaEquiv p.base)
  naturality := fun _ _ φ ↦ toFunctorOfPoints_naturality f g φ

/-- The component of `toFunctorOfPoints` at `T` sends a pair to the universe-lift
of the Yoneda equivalent of its base morphism. -/
theorem toFunctorOfPoints_app {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) (T : (Over S)ᵒᵖ)
    (p : Pair f g T.unop) :
    (toFunctorOfPoints f g).app T p = ULift.up (yonedaEquiv p.base) := sorry

/-- The canonical fibre is the categorical pullback. -/
def fiberPullbackIso {S : Scheme.{u}} {Z B : AlgebraicSpace S} (g : Z ⟶ B)
    {T : Over S} (a : ofOver T ⟶ B) : fiber g a ≅ pullback a g :=
  Iso.refl _

/-- The canonical comparison preserves the projection to the test scheme. -/
theorem fiberPullbackIso_hom_fst {S : Scheme.{u}} {Z B : AlgebraicSpace S}
    (g : Z ⟶ B) {T : Over S} (a : ofOver T ⟶ B) :
    (fiberPullbackIso g a).hom ≫ pullback.fst a g = fiberFst g a :=
  by exact Category.id_comp _

/-- The canonical comparison preserves the projection to `Z`. -/
theorem fiberPullbackIso_hom_snd {S : Scheme.{u}} {Z B : AlgebraicSpace S}
    (g : Z ⟶ B) {T : Over S} (a : ofOver T ⟶ B) :
    (fiberPullbackIso g a).hom ≫ pullback.snd a g = fiberSnd g a :=
  by exact Category.id_comp _

/-- The inverse comparison preserves the projection to the test scheme. -/
theorem fiberPullbackIso_inv_fst {S : Scheme.{u}} {Z B : AlgebraicSpace S}
    (g : Z ⟶ B) {T : Over S} (a : ofOver T ⟶ B) :
    (fiberPullbackIso g a).inv ≫ fiberFst g a = pullback.fst a g :=
  by exact Category.id_comp _

/-- The inverse comparison preserves the projection to `Z`. -/
theorem fiberPullbackIso_inv_snd {S : Scheme.{u}} {Z B : AlgebraicSpace S}
    (g : Z ⟶ B) {T : Over S} (a : ofOver T ⟶ B) :
    (fiberPullbackIso g a).inv ≫ fiberSnd g a = pullback.snd a g :=
  by exact Category.id_comp _

/-- Restriction of scalars satisfies fppf descent. -/
theorem isSheaf {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (restrictionOfScalars f g) := sorry

/-- The fppf sheaf of lifts to `X` over the base changes of `Z`. -/
def sheaf {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨restrictionOfScalars f g, isSheaf f g⟩

/-- Sections of restriction of scalars are pairs over the test scheme. -/
theorem sheaf_obj {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) (T : Over S) :
    (sheaf f g).obj.obj (op T) = Pair f g T := rfl

/-- The structure morphism of restriction of scalars records its base point. -/
def toBase {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B) :
    sheaf f g ⟶ toSheaf.obj B :=
  ObjectProperty.homMk (toFunctorOfPoints f g)

/-- The structure morphism has the same components as the presheaf projection. -/
theorem toBase_app {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) (T : (Over S)ᵒᵖ) :
    (toBase f g).hom.app T = (toFunctorOfPoints f g).app T := rfl

/-- The structure morphism sends a pair to the Yoneda point of its base morphism. -/
theorem toBase_spec {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) {T : Over S} (p : Pair f g T) :
    (toBase f g).hom.app (op T) p = ULift.up (yonedaEquiv p.base) := rfl

end AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
