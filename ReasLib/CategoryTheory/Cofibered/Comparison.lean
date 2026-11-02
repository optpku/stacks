/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import ReasLib.CategoryTheory.Cofibered.Fiber

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

private theorem homLift_op {F : Type uX} [Category.{vX} F] {p : F ⥤ C}
    {B A : C} {x y : F} {f : B ⟶ A} {α : x ⟶ y}
    (h : p.IsHomLift f α) : p.op.IsHomLift f.op α.op := by
  cases h
  exact IsHomLift.map (p := p.op) _

private theorem homLift_unop {F : Type uX} [Category.{vX} F] {p : F ⥤ C}
    {B A : Cᵒᵖ} {x y : Fᵒᵖ} {f : B ⟶ A} {α : x ⟶ y}
    (h : p.op.IsHomLift f α) : p.IsHomLift f.unop α.unop := by
  cases h
  exact IsHomLift.map (p := p) _

private theorem stronglyCocartesian_unop {F : Type uX} [Category.{vX} F]
    {p : F ⥤ C} {B A : Cᵒᵖ} {x y : Fᵒᵖ} {f : B ⟶ A} {α : x ⟶ y}
    (h : p.op.IsStronglyCartesian f α) : p.IsStronglyCocartesian f.unop α.unop := by
  refine { toIsHomLift := homLift_unop h.toIsHomLift
           universal_property' := ?_ }
  intro target base arrow arrowLift
  have oppositeLift : p.op.IsHomLift (base.op ≫ f) arrow.op := by
    simpa only [op_comp, Quiver.Hom.op_unop] using homLift_op arrowLift
  obtain ⟨factor, ⟨factorLift, factorization⟩, uniqueness⟩ :=
    @IsStronglyCartesian.universal_property' _ _ _ _ p.op _ _ _ _ f α h
      (op target) base.op arrow.op oppositeLift
  refine ⟨factor.unop, ⟨homLift_unop factorLift, ?_⟩, ?_⟩
  · exact congrArg Quiver.Hom.unop factorization
  · intro candidate candidateProperty
    apply Quiver.Hom.op_inj
    exact uniqueness candidate.op
      ⟨homLift_op candidateProperty.1, congrArg Quiver.Hom.op candidateProperty.2⟩

private theorem stronglyCartesian_of_homLift {F : Type uX} [Category.{vX} F]
    {p : F ⥤ C} [Functor.IsFibered.InGroupoids p]
    {B A : C} {x y : F} {f : B ⟶ A} {α : x ⟶ y}
    (h : p.IsHomLift f α) : p.IsStronglyCartesian f α := by
  cases h
  infer_instance

private theorem pushforwardFiberMap_fac {F : Type uX} [Category.{vX} F]
    (p : F ⥤ C) (χ : p.op.Cleavage) {B A : C} (f : B ⟶ A)
    {x y : p.Fiber B} (α : x ⟶ y) :
    (χ.cartesianHom f.op (toOpFiber p x)).unop ≫
        ((pushforwardFiberFunctor p χ f).map α).1 =
      α.1 ≫ (χ.cartesianHom f.op (toOpFiber p y)).unop := by
  have hx : p.op.IsStronglyCartesian f.op (χ.cartesianHom f.op (toOpFiber p x)) :=
    (χ.reindexLift f.op (toOpFiber p x)).isStronglyCartesian
  have hy : p.op.IsStronglyCartesian f.op (χ.cartesianHom f.op (toOpFiber p y)) :=
    (χ.reindexLift f.op (toOpFiber p y)).isStronglyCartesian
  have hα : p.op.IsHomLift (𝟙 (op B)) α.1.op := by
    simpa only [op_id] using homLift_op α.2
  have hcomp : p.op.IsHomLift f.op
      (χ.cartesianHom f.op (toOpFiber p y) ≫ α.1.op) :=
    @IsHomLift.comp_lift_id_right' _ _ _ _ p.op _ _ _ _ _ f.op
      (χ.cartesianHom f.op (toOpFiber p y)) hy.toIsHomLift (op B) α.1.op hα
  exact congrArg Quiver.Hom.unop
    (@IsStronglyCartesian.fac _ _ _ _ p.op _ _ _ _ f.op
      (χ.cartesianHom f.op (toOpFiber p x)) hx _ _ (𝟙 (op A)) f.op
      (Category.id_comp f.op).symm (χ.cartesianHom f.op (toOpFiber p y) ≫ α.1.op) hcomp)

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
    Y.p.IsStronglyCocartesian f (mapPushforwardHom φ χX f x) := by
  have hx : X.p.IsHomLift f (χX.cartesianHom f.op (toOpFiber X.p x)).unop :=
    homLift_unop (χX.reindexLift f.op
      (toOpFiber X.p x)).isStronglyCartesian.toIsHomLift
  have h : Y.p.IsHomLift f (mapPushforwardHom φ χX f x) := by
    unfold mapPushforwardHom
    exact @BasedFunctor.preserves_isHomLift _ _ X Y φ _ _ _ _ f _ hx
  exact stronglyCocartesian_unop (stronglyCartesian_of_homLift (homLift_op h))

/-- The chosen target pushforward of `φ.obj x` is strongly cocartesian. -/
theorem targetPushforwardHom_isStronglyCocartesian (φ : X ⥤ᵇ Y) (χY : Y.p.op.Cleavage)
    {B A : C} (f : B ⟶ A) (x : X.p.Fiber B) :
    Y.p.IsStronglyCocartesian f (targetPushforwardHom φ χY f x) := by
  exact stronglyCocartesian_unop (χY.reindexLift f.op
    (toOpFiber Y.p ((φ.fiberFunctor B).obj x))).isStronglyCartesian

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
    Y.p.IsHomLift (𝟙 A) (pushforwardCommIsoAmbient φ χX χY f x).hom := by
  exact @IsStronglyCocartesian.map_isHomLift _ _ _ _ Y.p _ _ _ _ f
    (mapPushforwardHom φ χX f x) (mapPushforwardHom_isStronglyCocartesian φ χX f x)
    _ _ (𝟙 A) f (Category.comp_id f).symm (targetPushforwardHom φ χY f x)
    (targetPushforwardHom_isStronglyCocartesian φ χY f x).toIsHomLift

/-- Objectwise fibre comparison `φ (f_* x) ≅ f_* (φ x)`. -/
noncomputable def pushforwardCommIsoComponent (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A)
    (x : X.p.Fiber B) :
    (φ.fiberFunctor A).obj ((pushforwardFiberFunctor X.p χX f).obj x) ≅
      (pushforwardFiberFunctor Y.p χY f).obj ((φ.fiberFunctor B).obj x) :=
  Fiber.isoMk (pushforwardCommIsoAmbient φ χX χY f x)
    (pushforwardCommIsoAmbient_hom_isHomLift φ χX χY f x)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the objectwise fibre comparison in the source fibre. -/
theorem pushforwardCommIsoComponent_naturality (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A)
    {x y : X.p.Fiber B} (α : x ⟶ y) :
    (pushforwardFiberFunctor X.p χX f ⋙ φ.fiberFunctor A).map α ≫
        (pushforwardCommIsoComponent φ χX χY f y).hom =
      (pushforwardCommIsoComponent φ χX χY f x).hom ≫
        (φ.fiberFunctor B ⋙ pushforwardFiberFunctor Y.p χY f).map α := by
  have source_fac :
      mapPushforwardHom φ χX f x ≫
          φ.map ((pushforwardFiberFunctor X.p χX f).map α).1 =
        φ.map α.1 ≫ mapPushforwardHom φ χX f y := by
    calc
      _ = φ.map ((χX.cartesianHom f.op (toOpFiber X.p x)).unop ≫
          ((pushforwardFiberFunctor X.p χX f).map α).1) :=
        (φ.toFunctor.map_comp _ _).symm
      _ = φ.map (α.1 ≫ (χX.cartesianHom f.op (toOpFiber X.p y)).unop) :=
        congrArg φ.map (pushforwardFiberMap_fac X.p χX f α)
      _ = _ := φ.toFunctor.map_comp _ _
  have target_fac :
      targetPushforwardHom φ χY f x ≫
          ((pushforwardFiberFunctor Y.p χY f).map ((φ.fiberFunctor B).map α)).1 =
        φ.map α.1 ≫ targetPushforwardHom φ χY f y :=
    pushforwardFiberMap_fac Y.p χY f ((φ.fiberFunctor B).map α)
  have component_fac (z : X.p.Fiber B) :
      mapPushforwardHom φ χX f z ≫ (pushforwardCommIsoAmbient φ χX χY f z).hom =
        targetPushforwardHom φ χY f z := by
    exact @IsStronglyCocartesian.fac _ _ _ _ Y.p _ _ _ _ f
      (mapPushforwardHom φ χX f z) (mapPushforwardHom_isStronglyCocartesian φ χX f z)
      _ _ (𝟙 A) f (Category.comp_id f).symm (targetPushforwardHom φ χY f z)
      (targetPushforwardHom_isStronglyCocartesian φ χY f z).toIsHomLift
  apply Fiber.hom_ext
  refine @IsStronglyCocartesian.ext _ _ _ _ Y.p _ _ _ _ f
    (mapPushforwardHom φ χX f x) (mapPushforwardHom_isStronglyCocartesian φ χX f x)
    _ _ (𝟙 A) _ _
    ((pushforwardFiberFunctor X.p χX f ⋙ φ.fiberFunctor A).map α ≫
      (pushforwardCommIsoComponent φ χX χY f y).hom).2
    ((pushforwardCommIsoComponent φ χX χY f x).hom ≫
      (φ.fiberFunctor B ⋙ pushforwardFiberFunctor Y.p χY f).map α).2 ?_
  change mapPushforwardHom φ χX f x ≫
      (φ.map ((pushforwardFiberFunctor X.p χX f).map α).1 ≫
        (pushforwardCommIsoAmbient φ χX χY f y).hom) =
    mapPushforwardHom φ χX f x ≫
      ((pushforwardCommIsoAmbient φ χX χY f x).hom ≫
        ((pushforwardFiberFunctor Y.p χY f).map ((φ.fiberFunctor B).map α)).1)
  have hsource := congrArg
    (fun k => k ≫ (pushforwardCommIsoAmbient φ χX χY f y).hom) source_fac
  have hsource' :
      mapPushforwardHom φ χX f x ≫
          (φ.map ((pushforwardFiberFunctor X.p χX f).map α).1 ≫
            (pushforwardCommIsoAmbient φ χX χY f y).hom) =
        φ.map α.1 ≫
          (mapPushforwardHom φ χX f y ≫
            (pushforwardCommIsoAmbient φ χX χY f y).hom) := by
    simpa only [Category.assoc] using hsource
  have hcomponent := congrArg (fun k => φ.map α.1 ≫ k) (component_fac y)
  have hcomponent' :
      φ.map α.1 ≫
          (mapPushforwardHom φ χX f y ≫
            (pushforwardCommIsoAmbient φ χX χY f y).hom) =
        φ.map α.1 ≫ targetPushforwardHom φ χY f y := hcomponent
  have htarget :
      φ.map α.1 ≫ targetPushforwardHom φ χY f y =
        targetPushforwardHom φ χY f x ≫
          ((pushforwardFiberFunctor Y.p χY f).map ((φ.fiberFunctor B).map α)).1 :=
    target_fac.symm
  have hcomponentX := congrArg
    (fun k => k ≫ ((pushforwardFiberFunctor Y.p χY f).map ((φ.fiberFunctor B).map α)).1)
    (component_fac x).symm
  have hcomponentX' :
      targetPushforwardHom φ χY f x ≫
          ((pushforwardFiberFunctor Y.p χY f).map ((φ.fiberFunctor B).map α)).1 =
        mapPushforwardHom φ χX f x ≫
          ((pushforwardCommIsoAmbient φ χX χY f x).hom ≫
            ((pushforwardFiberFunctor Y.p χY f).map ((φ.fiberFunctor B).map α)).1) := by
    simpa only [Category.assoc] using hcomponentX
  exact hsource'.trans (hcomponent'.trans (htarget.trans hcomponentX'))

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
    (pushforwardSquare φ χX χY f).fst = pushforwardFiberFunctor X.p χX f := rfl

/-- The second leg of `pushforwardSquare` is the fibre restriction of `φ` over `B`. -/
@[simp]
theorem pushforwardSquare_snd (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A) :
    (pushforwardSquare φ χX χY f).snd = φ.fiberFunctor B := rfl

/-- The structural 2-cell of `pushforwardSquare` is `pushforwardCommIso`. -/
@[simp]
theorem pushforwardSquare_iso (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A) :
    (pushforwardSquare φ χX χY f).iso = pushforwardCommIso φ χX χY f := rfl

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
      (pushforwardFiberFunctor X.p χX f).obj x := rfl

/-- The second projection of `pushforwardComparison` on objects is the fibre restriction of `φ`. -/
@[simp]
theorem pushforwardComparison_obj_snd (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A)
    (x : X.p.Fiber B) :
    ((pushforwardComparison φ χX χY f).obj x).snd =
      (φ.fiberFunctor B).obj x := rfl

/-- The structural isomorphism of `pushforwardComparison` on objects is the square's 2-cell. -/
@[simp]
theorem pushforwardComparison_obj_iso (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A)
    (x : X.p.Fiber B) :
    ((pushforwardComparison φ χX χY f).obj x).iso =
      (pushforwardSquare φ χX χY f).iso.app x := rfl

/-- Objects of `pushforwardComparison` record the two legs and the structural 2-cell. -/
theorem pushforwardComparison_spec (φ : X ⥤ᵇ Y)
    (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage) {B A : C} (f : B ⟶ A)
    (x : X.p.Fiber B) :
    ((pushforwardComparison φ χX χY f).obj x).fst =
        (pushforwardFiberFunctor X.p χX f).obj x ∧
      ((pushforwardComparison φ χX χY f).obj x).snd =
        (φ.fiberFunctor B).obj x ∧
      ((pushforwardComparison φ χX χY f).obj x).iso =
        (pushforwardSquare φ χX χY f).iso.app x :=
  ⟨rfl, rfl, rfl⟩

end CategoryTheory.BasedFunctor

