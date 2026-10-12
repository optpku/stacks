/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Intrinsic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import stacks_project.Chap96.Lemma_96_12_4_EtaleModules

/-!
# Small-étale comparison morphisms of module sheaves on a CFG

A morphism `φ : x ⟶ y` in a category fibred in groupoids over `(Sch/S)_fppf`
induces a comparison morphism of `𝒪_{U_étale}`-modules
`c_φ : a_small^*(F|_{V_étale}) ⟶ F|_{U_étale}` from the cartesian fill-in of
the pullback square of `a = (X.p.map φ).left`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite Limits
open Functor
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The object of `Over S` associated to an étale morphism `W ⟶ U` over the
scheme `U = (X.p.obj x).left`. -/
def etaleSlice {X : GroupoidsOver S} (x : X.total)
    (W : (X.p.obj x).left.Etale) : Over S :=
  Over.mk (W.hom ≫ (X.p.obj x).hom)

/-- The morphism `etaleSlice x W ⟶ X.p.obj x` in `Over S` with left component
`W.hom`. -/
def etaleSliceHom {X : GroupoidsOver S} (x : X.total)
    (W : (X.p.obj x).left.Etale) :
    etaleSlice x W ⟶ X.p.obj x :=
  Over.homMk W.hom

/-- The morphism of `Over S` objects induced by a morphism of étale schemes
over `U`. -/
def etaleSliceMap {X : GroupoidsOver S} (x : X.total)
    {W W' : (X.p.obj x).left.Etale} (g : W' ⟶ W) :
    etaleSlice x W' ⟶ etaleSlice x W :=
  Over.homMk g.left
    ((Category.assoc g.left W.hom (X.p.obj x).hom).symm.trans
      (congrArg (fun t => t ≫ (X.p.obj x).hom) g.w))

/-- The chosen cartesian lift of `x` along an étale morphism `W ⟶ U`. -/
def cartesianLift {X : GroupoidsOver S} (x : X.total)
    (W : (X.p.obj x).left.Etale) : X.total :=
  ((Cleavage.ofIsFibered X.p).lift (etaleSliceHom x W)).source

/-- The chosen cartesian arrow from `cartesianLift x W` to `x`. -/
def cartesianLiftHom {X : GroupoidsOver S} (x : X.total)
    (W : (X.p.obj x).left.Etale) :
    cartesianLift x W ⟶ x :=
  ((Cleavage.ofIsFibered X.p).lift (etaleSliceHom x W)).hom

/-- The chosen cartesian arrow is strongly cartesian over `etaleSliceHom x W`. -/
instance cartesianLiftHom_isStronglyCartesian {X : GroupoidsOver S}
    (x : X.total) (W : (X.p.obj x).left.Etale) :
    X.p.IsStronglyCartesian (etaleSliceHom x W) (cartesianLiftHom x W) :=
  ((Cleavage.ofIsFibered X.p).lift (etaleSliceHom x W)).isStronglyCartesian

/-- The ring map `𝒪_{U_étale}(W) ⟶ 𝒪_X(cartesianLift x W)` induced by the
identification of underlying schemes. -/
def restrictRingHom {X : GroupoidsOver S} (x : X.total)
    (W : (X.p.obj x).left.Etale) :
    (Scheme.Etale.Small.structureSheaf (X.p.obj x).left).obj.obj (op W) ⟶
      (etaleStructureSheaf X).obj.obj (op (cartesianLift x W)) :=
  (forget₂ CommRingCat RingCat).map
    (Scheme.Γ.map
      (eqToHom
        (congrArg Over.left
          (IsHomLift.domain_eq X.p (etaleSliceHom x W)
            (cartesianLiftHom x W)))).op)

/-- Triangle identity for `etaleSliceMap` and `etaleSliceHom`.
This is a `def` because the equality is an argument of
`IsStronglyCartesian.map`. -/
def etaleSliceHom_comp {X : GroupoidsOver S} (x : X.total)
    {W W' : (X.p.obj x).left.Etale} (g : W' ⟶ W) :
    etaleSliceHom x W' = etaleSliceMap x g ≫ etaleSliceHom x W :=
  CostructuredArrow.hom_ext _ _ g.w.symm

/-- Restriction of the cartesian lift of `x` along a morphism of étale schemes
over `U`. -/
def cartesianLiftMap {X : GroupoidsOver S} (x : X.total)
    {W W' : (X.p.obj x).left.Etale} (g : W' ⟶ W) :
    cartesianLift x W' ⟶ cartesianLift x W :=
  IsStronglyCartesian.map X.p (etaleSliceHom x W) (cartesianLiftHom x W)
    (etaleSliceHom_comp x g) (cartesianLiftHom x W')


/-- Restriction of scalars along a composite ring homomorphism, on objects. -/
def restrictScalarsCompIso {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) (M : ModuleCat.{u} T) :
    (ModuleCat.restrictScalars.{u} (g.comp f)).obj M ≅
      (ModuleCat.restrictScalars f).obj ((ModuleCat.restrictScalars g).obj M) :=
  ModuleCat.restrictScalarsComp'App f g (g.comp f) rfl M

/-- The ring presheaf on `U_étale` with value `𝒪_X` at the cartesian lift of
`x`. -/
def restrictEtaleRing {X : GroupoidsOver S} (x : X.total) :
    ((X.p.obj x).left.Etale)ᵒᵖ ⥤ RingCat.{u} where
  obj W := (etaleStructureSheaf X).obj.obj (op (cartesianLift x W.unop))
  map f := (etaleStructureSheaf X).obj.map (cartesianLiftMap x f.unop).op
  map_id := sorry
  map_comp := sorry

/-- `F` evaluated at cartesian lifts of `x`, as a presheaf of modules over
`restrictEtaleRing x`. -/
def restrictEtaleModules {X : GroupoidsOver S}
    (F : SheafOfModules.{u} (etaleStructureSheaf X)) (x : X.total) :
    PresheafOfModules.{u} (restrictEtaleRing x) where
  obj W := F.val.obj (op (cartesianLift x W.unop))
  map f := F.val.map (cartesianLiftMap x f.unop).op
  map_id := sorry
  map_comp := sorry

/-- The natural map of ring presheaves `𝒪_{U_étale} ⟶ restrictEtaleRing x`. -/
def restrictRingNatTrans {X : GroupoidsOver S} (x : X.total) :
    (Scheme.Etale.Small.structureSheaf (X.p.obj x).left).obj ⟶
      restrictEtaleRing x where
  app W := restrictRingHom x W.unop
  naturality := sorry

/-- The small-étale restriction `F|_{U_étale}` as a sheaf of
`𝒪_{U_étale}`-modules. -/
def restrictEtale {X : GroupoidsOver S}
    (F : SheafOfModules.{u} (etaleStructureSheaf X)) (x : X.total) :
    SheafOfModules.{u} (Scheme.Etale.Small.structureSheaf (X.p.obj x).left) where
  val :=
    (PresheafOfModules.restrictScalars (restrictRingNatTrans x)).obj
      (restrictEtaleModules F x)
  isSheaf := sorry

/-- At `W` étale over `U`, the value of `restrictEtale F x` is `F` at a
cartesian lift of `x`, with scalars restricted along `restrictRingHom`. -/
theorem restrictEtale_obj {X : GroupoidsOver S}
    (F : SheafOfModules.{u} (etaleStructureSheaf X)) (x : X.total)
    (W : (X.p.obj x).left.Etale) :
    (restrictEtale F x).val.obj (op W) =
      (ModuleCat.restrictScalars (restrictRingHom x W).hom).obj
        (F.val.obj (op (cartesianLift x W))) :=
  sorry

/-- Triangle identity for the base-change projection `U' ⟶ V'` in `Over S`.
This is a `def` because the equality is an argument of `Over.homMk`. -/
def baseFill_w {X : GroupoidsOver S} {x y : X.total} (φ : x ⟶ y)
    (V' : (X.p.obj y).left.Etale) :
    pullback.fst V'.hom (X.p.map φ).left ≫ (V'.hom ≫ (X.p.obj y).hom) =
      ((Scheme.smallEtalePullback (X.p.map φ).left).obj V').hom ≫
        (X.p.obj x).hom :=
  (Category.assoc (pullback.fst V'.hom (X.p.map φ).left) V'.hom
      (X.p.obj y).hom).symm.trans
    ((congrArg (fun t => t ≫ (X.p.obj y).hom)
        (pullback.condition (f := V'.hom) (g := (X.p.map φ).left))).trans
      ((Category.assoc (pullback.snd V'.hom (X.p.map φ).left)
          (X.p.map φ).left (X.p.obj y).hom).trans
        ((congrArg (fun t => pullback.snd V'.hom (X.p.map φ).left ≫ t)
            (X.p.map φ).w).trans
          (congrArg (fun t => t ≫ (X.p.obj x).hom)
            (MorphismProperty.Over.pullback_obj_hom (@Etale) ⊤
              (X.p.map φ).left V')).symm)))

/-- The morphism `U' ⟶ V'` in `Over S` from the fibre product
`U' = V' ×_V U` of an étale morphism `V' ⟶ V` along `a = (X.p.map φ).left`. -/
def baseFill {X : GroupoidsOver S} {x y : X.total} (φ : x ⟶ y)
    (V' : (X.p.obj y).left.Etale) :
    etaleSlice x ((Scheme.smallEtalePullback (X.p.map φ).left).obj V') ⟶
      etaleSlice y V' :=
  Over.homMk (pullback.fst V'.hom (X.p.map φ).left) (baseFill_w φ V')

/-- The pullback square of `a = (X.p.map φ).left` commutes in `Over S`.
This is a `def` because the equality is an argument of
`IsStronglyCartesian.map`. -/
def fillIn_comm {X : GroupoidsOver S} {x y : X.total} (φ : x ⟶ y)
    (V' : (X.p.obj y).left.Etale) :
    etaleSliceHom x ((Scheme.smallEtalePullback (X.p.map φ).left).obj V') ≫
        X.p.map φ =
      baseFill φ V' ≫ etaleSliceHom y V' :=
  CostructuredArrow.hom_ext _ _
    ((congrArg (fun t => t ≫ (X.p.map φ).left)
        (MorphismProperty.Over.pullback_obj_hom (@Etale) ⊤
          (X.p.map φ).left V')).trans
      (pullback.condition (f := V'.hom) (g := (X.p.map φ).left)).symm)

/-- The cartesian fill-in `φ' : x' ⟶ y'` of the pullback square of `φ` along
an étale morphism `V' ⟶ V`. -/
def fillIn {X : GroupoidsOver S} {x y : X.total} (φ : x ⟶ y)
    (V' : (X.p.obj y).left.Etale) :
    cartesianLift x ((Scheme.smallEtalePullback (X.p.map φ).left).obj V') ⟶
      cartesianLift y V' :=
  IsStronglyCartesian.map X.p (etaleSliceHom y V') (cartesianLiftHom y V')
    (fillIn_comm φ V')
    (cartesianLiftHom x ((Scheme.smallEtalePullback (X.p.map φ).left).obj V') ≫
      φ)

/-- Compatibility of the cartesian fill-in with small-étale structure maps
and the restriction ring maps: `φring.comp αy = αx.comp a_small^♯`. -/
theorem restrictRingHom_fillIn {X : GroupoidsOver S} {x y : X.total}
    (φ : x ⟶ y) (V' : (X.p.obj y).left.Etale) :
    ((etaleStructureSheaf X).obj.map (fillIn φ V').op).hom.comp
        (restrictRingHom y V').hom =
      (restrictRingHom x
          ((Scheme.smallEtalePullback (X.p.map φ).left).obj V')).hom.comp
        ((Scheme.Etale.Small.ringedHom (X.p.map φ).left).structureSheafMap.hom.app
          (op V')).hom :=
  sorry

/-- The push-form comparison
`c_φ : F|_{V_étale} ⟶ a_small,*(F|_{U_étale})` of `𝒪_{V_étale}`-modules,
with components `F(φ')` on cartesian fill-ins. -/
def moduleComparisonPushforward {X : GroupoidsOver S} {x y : X.total}
    (φ : x ⟶ y) (F : SheafOfModules.{u} (etaleStructureSheaf X)) :
    restrictEtale F y ⟶
      ((Scheme.Etale.Small.ringedHom (X.p.map φ).left).modulePushforward.{u}).obj
        (restrictEtale F x) where
  val :=
    { app := fun V' ↦
        let a := (X.p.map φ).left
        let U' := (Scheme.smallEtalePullback a).obj V'.unop
        let αy := (restrictRingHom y V'.unop).hom
        let αx := (restrictRingHom x U').hom
        let φring := ((etaleStructureSheaf X).obj.map (fillIn φ V'.unop).op).hom
        let aSharp :=
          ((Scheme.Etale.Small.ringedHom a).structureSheafMap.hom.app V').hom
        (ModuleCat.restrictScalars αy).map (F.val.map (fillIn φ V'.unop).op) ≫
          (restrictScalarsCompIso αy φring _).inv ≫
            (ModuleCat.restrictScalarsCongr
                (restrictRingHom_fillIn φ V'.unop)).hom.app _ ≫
              (restrictScalarsCompIso aSharp αx _).hom
      naturality := sorry }

/-- On an étale object `V' ⟶ V`, the push-form comparison has the same
underlying abelian map as `F(φ')`. -/
theorem moduleComparisonPushforward_app {X : GroupoidsOver S} {x y : X.total}
    (φ : x ⟶ y) (F : SheafOfModules.{u} (etaleStructureSheaf X))
    (V' : (X.p.obj y).left.Etale) (m : (restrictEtale F y).val.obj (op V')) :
    (moduleComparisonPushforward φ F).val.app (op V') m =
      (F.val.map (fillIn φ V').op).hom m :=
  sorry

/-- The comparison morphism
`c_φ : a_small^*(F|_{V_étale}) ⟶ F|_{U_étale}` of `𝒪_{U_étale}`-modules,
obtained as the adjunct of `moduleComparisonPushforward`. -/
def moduleComparison {X : GroupoidsOver S} {x y : X.total} (φ : x ⟶ y)
    (F : SheafOfModules.{u} (etaleStructureSheaf X)) :
    ((Scheme.Etale.Small.ringedHom (X.p.map φ).left).modulePullback.{u}).obj
        (restrictEtale F y) ⟶
      restrictEtale F x :=
  (modulePullbackHomEquiv (Scheme.Etale.Small.ringedHom (X.p.map φ).left)
      (restrictEtale F y) (restrictEtale F x)).symm
    (moduleComparisonPushforward φ F)

/-- `moduleComparison φ F` is the adjunct of `moduleComparisonPushforward φ F`
along the small-étale pullback-pushforward adjunction. -/
theorem moduleComparison_adjunct {X : GroupoidsOver S} {x y : X.total}
    (φ : x ⟶ y) (F : SheafOfModules.{u} (etaleStructureSheaf X)) :
    modulePullbackHomEquiv (Scheme.Etale.Small.ringedHom (X.p.map φ).left)
        (restrictEtale F y) (restrictEtale F x)
        (moduleComparison φ F) =
      moduleComparisonPushforward φ F :=
  sorry

/-- Source-semantic characterisation: on an étale `V' ⟶ V`, the push form of
`c_φ` acts as `F(φ')` for the cartesian fill-in of `U' = V' ×_V U`. -/
theorem moduleComparison_spec {X : GroupoidsOver S} {x y : X.total}
    (φ : x ⟶ y) (F : SheafOfModules.{u} (etaleStructureSheaf X))
    (V' : (X.p.obj y).left.Etale) (m : (restrictEtale F y).val.obj (op V')) :
    (moduleComparisonPushforward φ F).val.app (op V') m =
      (F.val.map (fillIn φ V').op).hom m :=
  sorry

/-- Unfolding `moduleComparison` as the adjunct of the push form. -/
theorem moduleComparison_app {X : GroupoidsOver S} {x y : X.total}
    (φ : x ⟶ y) (F : SheafOfModules.{u} (etaleStructureSheaf X)) :
    moduleComparison φ F =
      (modulePullbackHomEquiv (Scheme.Etale.Small.ringedHom (X.p.map φ).left)
          (restrictEtale F y) (restrictEtale F x)).symm
        (moduleComparisonPushforward φ F) :=
  sorry

end AlgebraicGeometry.GroupoidsOver

