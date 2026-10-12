/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Lemma_67_27_3_QuasiFinite
public import stacks_project.Chap69.Lemma_69_11_2_Flat_base_change_BaseChange
public import stacks_project.Chap99.Situation_99_5_1

/-!
# Quasi-finite pushforward on fibres of the coherent stack

A morphism `π : X ⟶ Y` of algebraic spaces over `B` induces a comparison
`X_T ⟶ Y_T` on fibres. When `π` is quasi-finite and both structure maps to `B`
are separated and of finite presentation, pushforward of modules along this
comparison sends objects of `CohStack (π ≫ y)` to objects of `CohStack y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- The comparison `X_T ⟶ Y_T` induced by `π : X ⟶ Y` over `B`. -/
def fiberComparison (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B) :
    fiber (π ≫ y) σ ⟶ fiber y σ :=
  pullback.map (π ≫ y) σ.hom y σ.hom π
    (𝟙 ((ofOverFunctor S).obj σ.left)) (𝟙 B) (Category.comp_id (π ≫ y))
    ((Category.comp_id σ.hom).trans (Category.id_comp σ.hom).symm)

/-- The fibre comparison commutes with the projections to `X` and `Y`. -/
theorem fiberComparison_fst (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B) :
    fiberComparison π y σ ≫ pullback.fst y σ.hom =
      pullback.fst (π ≫ y) σ.hom ≫ π :=
  pullback.lift_fst _ _ _

/-- The fibre comparison commutes with the projections to the test scheme. -/
theorem fiberComparison_snd (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B) :
    fiberComparison π y σ ≫ pullback.snd y σ.hom =
      pullback.snd (π ≫ y) σ.hom ≫ 𝟙 ((ofOverFunctor S).obj σ.left) :=
  pullback.lift_snd _ _ _

/-- The fibre comparison is the map of pullbacks induced by `π` and the identity
on the test scheme. -/
theorem fiberComparison_spec (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B) :
    fiberComparison π y σ ≫ pullback.fst y σ.hom =
        pullback.fst (π ≫ y) σ.hom ≫ π ∧
      fiberComparison π y σ ≫ pullback.snd y σ.hom =
        pullback.snd (π ≫ y) σ.hom :=
  ⟨fiberComparison_fst π y σ,
    (fiberComparison_snd π y σ).trans
      (Category.comp_id (pullback.snd (π ≫ y) σ.hom))⟩

/-- First-projection compatibility of the fibre comparison square. -/
theorem fiberComparison_comm_fst (π : X ⟶ Y) (y : Y ⟶ B)
    {σ τ : SchemesOver B} (h : σ ⟶ τ) :
    (fiberMap (π ≫ y) h ≫ fiberComparison π y τ) ≫ pullback.fst y τ.hom =
      (fiberComparison π y σ ≫ fiberMap y h) ≫ pullback.fst y τ.hom :=
  Eq.trans
    (Eq.trans (Category.assoc _ _ _)
      (Eq.trans
        (congrArg (fun φ => fiberMap (π ≫ y) h ≫ φ) (fiberComparison_fst π y τ))
        (Eq.trans (Eq.symm (Category.assoc _ _ _))
          (congrArg (fun φ => φ ≫ π)
            ((pullback.lift_fst _ _ _).trans
              (Category.comp_id (pullback.fst (π ≫ y) σ.hom)))))))
    (Eq.symm
      (Eq.trans (Category.assoc _ _ _)
        (Eq.trans
          (congrArg (fun φ => fiberComparison π y σ ≫ φ)
            ((pullback.lift_fst _ _ _).trans (Category.comp_id (pullback.fst y σ.hom))))
          (fiberComparison_fst π y σ))))

/-- Second-projection compatibility of the fibre comparison square. -/
theorem fiberComparison_comm_snd (π : X ⟶ Y) (y : Y ⟶ B)
    {σ τ : SchemesOver B} (h : σ ⟶ τ) :
    (fiberMap (π ≫ y) h ≫ fiberComparison π y τ) ≫ pullback.snd y τ.hom =
      (fiberComparison π y σ ≫ fiberMap y h) ≫ pullback.snd y τ.hom :=
  Eq.trans
    (Eq.trans (Category.assoc _ _ _)
      (Eq.trans
        (congrArg (fun φ => fiberMap (π ≫ y) h ≫ φ) (fiberComparison_snd π y τ))
        (Eq.trans
          (congrArg (fun φ => fiberMap (π ≫ y) h ≫ φ)
            (Category.comp_id (pullback.snd (π ≫ y) τ.hom)))
          (pullback.lift_snd _ _ _))))
    (Eq.symm
      (Eq.trans (Category.assoc _ _ _)
        (Eq.trans
          (congrArg (fun φ => fiberComparison π y σ ≫ φ) (pullback.lift_snd _ _ _))
          (Eq.trans (Eq.symm (Category.assoc _ _ _))
            (Eq.trans
              (congrArg (fun φ => φ ≫ (ofOverFunctor S).map h.left)
                (fiberComparison_snd π y σ))
              (congrArg (fun φ => φ ≫ (ofOverFunctor S).map h.left)
                (Category.comp_id (pullback.snd (π ≫ y) σ.hom))))))))

/-- The fibre comparison square commutes. -/
theorem fiberComparison_comm (π : X ⟶ Y) (y : Y ⟶ B)
    {σ τ : SchemesOver B} (h : σ ⟶ τ) :
    fiberMap (π ≫ y) h ≫ fiberComparison π y τ =
      fiberComparison π y σ ≫ fiberMap y h :=
  pullback.hom_ext (fiberComparison_comm_fst π y h) (fiberComparison_comm_snd π y h)

/-- The fibre comparison square is a pullback. -/
theorem fiberComparison_isPullback (π : X ⟶ Y) (y : Y ⟶ B)
    {σ τ : SchemesOver B} (h : σ ⟶ τ) :
    IsPullback (fiberMap (π ≫ y) h) (fiberComparison π y σ)
      (fiberComparison π y τ) (fiberMap y h) where
  w := fiberComparison_comm π y h
  isLimit' := sorry

/-- Pushforward of a coherent module on `X_T` along the fibre comparison `X_T ⟶ Y_T`. -/
def Obj.pushforward (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (x : Obj (π ≫ y)) : Obj y where
  σ := x.σ
  module := (Modules.pushforward (fiberComparison π y x.σ)).obj x.module
  isFinitePresentation := sorry
  isFlat := sorry
  hasProperSupport := sorry

/-- Objectwise pushforward preserves the underlying test scheme. -/
theorem Obj.pushforward_σ (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (x : Obj (π ≫ y)) :
    (Obj.pushforward π y x).σ = x.σ :=
  sorry

/-- Objectwise pushforward applies `π_{T,*}` to the module on the fibre. -/
theorem Obj.pushforward_module (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (x : Obj (π ≫ y)) :
    (Obj.pushforward π y x).module =
      (Modules.pushforward (fiberComparison π y x.σ)).obj x.module :=
  sorry

/-- The pushed module remains of finite presentation, flat over the test scheme,
and with proper support. -/
theorem Obj.pushforward_spec (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (x : Obj (π ≫ y)) :
    (Obj.pushforward π y x).module.IsFinitePresentation ∧
      flatOver (Obj.pushforward π y x).module (fiberToBase y x.σ) ∧
      Modules.HasProperSupportOver (fiberToBase y x.σ)
        (Obj.pushforward π y x).module :=
  sorry

/-- Forward base-change comparison
`(Y_{T'} → Y_T)^* π_{T,*} F ⟶ π_{T',*} (X_{T'} → X_T)^* F`. -/
def fiberPushforwardBaseChangeHom (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] {σ τ : SchemesOver B} (h : σ ⟶ τ)
    (F : (fiber (π ≫ y) τ).Modules) :
    (Modules.pullback (fiberMap y h)).obj
        ((Modules.pushforward (fiberComparison π y τ)).obj F) ⟶
      (Modules.pushforward (fiberComparison π y σ)).obj
        ((Modules.pullback (fiberMap (π ≫ y) h)).obj F) :=
  (Modules.pushforwardBaseChangeNatTrans (fiberComparison_isPullback π y h)).app F

/-- The underived base-change comparison along the fibre square is an
isomorphism on the module of an object of `CohStack (π ≫ y)`. -/
instance instIsIso_fiberPushforwardBaseChangeHom (π : X ⟶ Y) (y : Y ⟶ B)
    [QuasiFinite π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] (x : Obj (π ≫ y))
    {σ : SchemesOver B} (h : σ ⟶ x.σ) :
    IsIso (fiberPushforwardBaseChangeHom π y h x.module) :=
  sorry

/-- Base-change isomorphism on a `CohStack` object
`(Y_{T'} → Y_T)^* π_{T,*} F ≅ π_{T',*} (X_{T'} → X_T)^* F`. -/
def fiberPushforwardBaseChangeIso (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (x : Obj (π ≫ y)) {σ : SchemesOver B}
    (h : σ ⟶ x.σ) :
    (Modules.pullback (fiberMap y h)).obj
        ((Modules.pushforward (fiberComparison π y x.σ)).obj x.module) ≅
      (Modules.pushforward (fiberComparison π y σ)).obj
        ((Modules.pullback (fiberMap (π ≫ y) h)).obj x.module) :=
  asIso (fiberPushforwardBaseChangeHom π y h x.module)

/-- The forward map of `fiberPushforwardBaseChangeIso` is the underived
base-change mate of the fibre comparison square at `x.module`. -/
theorem fiberPushforwardBaseChangeIso_hom (π : X ⟶ Y) (y : Y ⟶ B)
    [QuasiFinite π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] (x : Obj (π ≫ y))
    {σ : SchemesOver B} (h : σ ⟶ x.σ) :
    (fiberPushforwardBaseChangeIso π y x h).hom =
      fiberPushforwardBaseChangeHom π y h x.module :=
  sorry

/-- The morphism of `CohStack` objects induced by a fibrewise pushforward of
the module isomorphism along `π_{T,*}`. -/
def mapHom (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] {x x' : Obj (π ≫ y)} (α : Hom x x') :
    Hom (Obj.pushforward π y x) (Obj.pushforward π y x') :=
  homMk α.base
    (fiberPushforwardBaseChangeIso π y x' α.base ≪≫
      (Modules.pushforward (fiberComparison π y x.σ)).mapIso α.iso)

/-- The total functor of fibrewise quasi-finite pushforward
`CohStack (π ≫ y) ⥤ CohStack y`. -/
def mapFunctor (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] :
    CohStack (π ≫ y) ⥤ CohStack y where
  obj := Obj.pushforward π y
  map α := mapHom π y α
  map_id := sorry
  map_comp := sorry

/-- `mapFunctor` lies strictly over `Over S`. -/
theorem mapFunctor_p (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] :
    mapFunctor π y ⋙ p y = p (π ≫ y) :=
  sorry

/-- Objectwise, `mapFunctor` is `Obj.pushforward`. -/
theorem mapFunctor_obj (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (x : CohStack (π ≫ y)) :
    (mapFunctor π y).obj x = Obj.pushforward π y x :=
  sorry

/-- `mapFunctor` preserves the underlying test scheme. -/
theorem mapFunctor_obj_σ (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (x : CohStack (π ≫ y)) :
    ((mapFunctor π y).obj x).σ = x.σ :=
  sorry

/-- `mapFunctor` sends a module `F` on `X_T` to `π_{T,*} F` on `Y_T`. -/
theorem mapFunctor_obj_module (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (x : CohStack (π ≫ y)) :
    ((mapFunctor π y).obj x).module =
      (Modules.pushforward (fiberComparison π y x.σ)).obj x.module :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
