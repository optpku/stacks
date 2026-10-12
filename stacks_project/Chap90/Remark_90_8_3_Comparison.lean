/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass

/-!
# Mixed fibre squares of a based functor and chosen pushforwards

A based functor `φ : X ⥤ᵇ Y` and chosen pushforwards along `f : B ⟶ A` determine a
2-commutative square of fibre categories. The induced comparison lands in the
categorical pullback `(φ.fiberFunctor A) ⊡ (pushforwardFiberFunctor Y.p χY f)`.
-/

@[expose] public section

open CategoryTheory Category Limits CategoricalPullback Opposite Functor
open scoped CategoricalPullback BasedFunctor

universe u v uX vX uY vY

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
variable [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]

namespace CategoryTheory.BasedFunctor

/-- The image under `φ` of the chosen pushforward of `x` along `f`. -/
noncomputable def mapPushforwardHom (φ : X ⥤ᵇ Y) (χX : X.p.op.Cleavage)
    {B A : C} (f : B ⟶ A) (x : X.p.Fiber B) :
    φ.obj x.1 ⟶
      ((φ.fiberFunctor A).obj ((pushforwardFiberFunctor X.p χX f).obj x)).1 :=
  φ.map (χX.cartesianHom f.op (toOpFiber X.p x)).unop

/-- The chosen pushforward of `φ.obj x` along `f`. -/
noncomputable def targetPushforwardHom (φ : X ⥤ᵇ Y) (χY : Y.p.op.Cleavage)
    {B A : C} (f : B ⟶ A) (x : X.p.Fiber B) :
    ((φ.fiberFunctor B).obj x).1 ⟶
      ((pushforwardFiberFunctor Y.p χY f).obj ((φ.fiberFunctor B).obj x)).1 :=
  (χY.cartesianHom f.op (toOpFiber Y.p ((φ.fiberFunctor B).obj x))).unop

/-- The image of a chosen source pushforward under `φ` is strongly cocartesian. -/
theorem mapPushforwardHom_isStronglyCocartesian (φ : X ⥤ᵇ Y) (χX : X.p.op.Cleavage)
    {B A : C} (f : B ⟶ A) (x : X.p.Fiber B) :
    Y.p.IsStronglyCocartesian f (mapPushforwardHom φ χX f x) := sorry

/-- The chosen target pushforward of `φ.obj x` is strongly cocartesian. -/
theorem targetPushforwardHom_isStronglyCocartesian (φ : X ⥤ᵇ Y) (χY : Y.p.op.Cleavage)
    {B A : C} (f : B ⟶ A) (x : X.p.Fiber B) :
    Y.p.IsStronglyCocartesian f (targetPushforwardHom φ χY f x) := sorry

/-- Ambient comparison of the two strongly cocartesian arrows from `φ.obj x`. -/
noncomputable def pushforwardCommIsoAmbient (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A)
    (x : X.p.Fiber B) :
    ((φ.fiberFunctor A).obj ((pushforwardFiberFunctor X.p χX f).obj x)).1 ≅
      ((pushforwardFiberFunctor Y.p χY f).obj ((φ.fiberFunctor B).obj x)).1 :=
  @IsStronglyCocartesian.codomainIsoOfBaseIso _ _ _ _ Y.p
    B A A (φ.obj x.1)
    ((φ.fiberFunctor A).obj ((pushforwardFiberFunctor X.p χX f).obj x)).1
    ((pushforwardFiberFunctor Y.p χY f).obj ((φ.fiberFunctor B).obj x)).1
    f f (Iso.refl A) (Category.comp_id f).symm
    (mapPushforwardHom φ χX f x) (targetPushforwardHom φ χY f x)
    (mapPushforwardHom_isStronglyCocartesian φ χX f x)
    (targetPushforwardHom_isStronglyCocartesian φ χY f x)

/-- The ambient comparison lies over the identity of the pushforward base. -/
theorem pushforwardCommIsoAmbient_hom_isHomLift (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A)
    (x : X.p.Fiber B) :
    Y.p.IsHomLift (𝟙 A) (pushforwardCommIsoAmbient φ χX χY f x).hom := sorry

/-- Objectwise fibre comparison `φ (f_* x) ≅ f_* (φ x)`. -/
noncomputable def pushforwardCommIsoComponent (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A)
    (x : X.p.Fiber B) :
    (φ.fiberFunctor A).obj ((pushforwardFiberFunctor X.p χX f).obj x) ≅
      (pushforwardFiberFunctor Y.p χY f).obj ((φ.fiberFunctor B).obj x) :=
  Fiber.isoMk (pushforwardCommIsoAmbient φ χX χY f x)
    (pushforwardCommIsoAmbient_hom_isHomLift φ χX χY f x)

/-- Naturality of the objectwise fibre comparison in the source fibre. -/
theorem pushforwardCommIsoComponent_naturality (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A)
    {x y : X.p.Fiber B} (α : x ⟶ y) :
    (pushforwardFiberFunctor X.p χX f ⋙ φ.fiberFunctor A).map α ≫
        (pushforwardCommIsoComponent φ χX χY f y).hom =
      (pushforwardCommIsoComponent φ χX χY f x).hom ≫
        (φ.fiberFunctor B ⋙ pushforwardFiberFunctor Y.p χY f).map α := sorry

/-- The 2-cell of fibre functors associated to `φ` and chosen pushforwards along `f`. -/
noncomputable def pushforwardCommIso (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A) :
    pushforwardFiberFunctor X.p χX f ⋙ φ.fiberFunctor A ≅
      φ.fiberFunctor B ⋙ pushforwardFiberFunctor Y.p χY f :=
  NatIso.ofComponents (pushforwardCommIsoComponent φ χX χY f)
    (pushforwardCommIsoComponent_naturality φ χX χY f)

/-- The 2-commutative square of fibre categories determined by `φ` and pushforwards along `f`. -/
noncomputable def pushforwardSquare (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A) :
    CatCommSqOver (φ.fiberFunctor A) (pushforwardFiberFunctor Y.p χY f)
      (X.p.Fiber B) where
  fst := pushforwardFiberFunctor X.p χX f
  snd := φ.fiberFunctor B
  iso := pushforwardCommIso φ χX χY f

/-- The first leg of `pushforwardSquare` is pushforward along `f` in the source. -/
@[simp]
theorem pushforwardSquare_fst (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A) :
    (pushforwardSquare φ χX χY f).fst = pushforwardFiberFunctor X.p χX f := sorry

/-- The second leg of `pushforwardSquare` is the fibre restriction of `φ` over `B`. -/
@[simp]
theorem pushforwardSquare_snd (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A) :
    (pushforwardSquare φ χX χY f).snd = φ.fiberFunctor B := sorry

/-- The structural 2-cell of `pushforwardSquare` is `pushforwardCommIso`. -/
@[simp]
theorem pushforwardSquare_iso (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A) :
    (pushforwardSquare φ χX χY f).iso = pushforwardCommIso φ χX χY f := sorry

/-- The induced functor `X.p.Fiber B ⥤ (φ.fiberFunctor A) ⊡ (pushforwardFiberFunctor Y.p χY f)`. -/
noncomputable def pushforwardComparison (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A) :
    X.p.Fiber B ⥤
      (φ.fiberFunctor A) ⊡ (pushforwardFiberFunctor Y.p χY f) :=
  (pushforwardSquare φ χX χY f).comparison

/-- The first projection of `pushforwardComparison` on objects is the source pushforward. -/
@[simp]
theorem pushforwardComparison_obj_fst (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A)
    (x : X.p.Fiber B) :
    ((pushforwardComparison φ χX χY f).obj x).fst =
      (pushforwardFiberFunctor X.p χX f).obj x := sorry

/-- The second projection of `pushforwardComparison` on objects is the fibre restriction of `φ`. -/
@[simp]
theorem pushforwardComparison_obj_snd (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A)
    (x : X.p.Fiber B) :
    ((pushforwardComparison φ χX χY f).obj x).snd =
      (φ.fiberFunctor B).obj x := sorry

/-- The structural isomorphism of `pushforwardComparison` on objects is the square's 2-cell. -/
@[simp]
theorem pushforwardComparison_obj_iso (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A)
    (x : X.p.Fiber B) :
    ((pushforwardComparison φ χX χY f).obj x).iso =
      (pushforwardSquare φ χX χY f).iso.app x := sorry

/-- Objects of `pushforwardComparison` record the two legs and the structural 2-cell. -/
theorem pushforwardComparison_spec (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A)
    (x : X.p.Fiber B) :
    ((pushforwardComparison φ χX χY f).obj x).fst =
        (pushforwardFiberFunctor X.p χX f).obj x ∧
      ((pushforwardComparison φ χX χY f).obj x).snd =
        (φ.fiberFunctor B).obj x ∧
      ((pushforwardComparison φ χX χY f).obj x).iso =
        (pushforwardSquare φ χX χY f).iso.app x := sorry

end CategoryTheory.BasedFunctor

