module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.MorphismProperty.Representable.ChangeOfBase
public import ReasLib.CategoryTheory.MorphismProperty.Representable.ChangeOfSource
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor
public import ReasLib.AlgebraicGeometry.Polarized.SpaceOver
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.OfPresheaf
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.InSets.Bicategory
public import ReasLib.CategoryTheory.Fibered.InSets.Forgetful

/-!
# Fibrewise base change of polarized algebraic-space families

A polarized family `(X ⟶ T, L)` over an algebraic space `T` over `Spec ℤ` determines a based
functor `S_T ⥤ᵇ Polarized` by sending a scheme-point of `T` to the representing scheme
`X_U ⟶ U` with the restricted line bundle.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry hiding QuasiSeparated QuasiCompact LocallyOfFinitePresentation Flat
open AlgebraicGeometry.AlgebraicSpace hiding RelativelyAmple
open AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
open Functor.relativelyRepresentable
open scoped CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- The category fibred in groupoids associated to an algebraic space over `Spec ℤ`. -/
def spaceStack (T : AlgebraicSpace specZ) :
    FiberedCategoryOver.Groupoids (Over specZ.{u}) :=
  (FiberedCategoryOver.Sets.toGroupoids (Over specZ.{u})).obj
    ((FiberedCategoryOver.Sets.ofPresheaf (Over specZ.{u})).obj T.functorOfPoints)

/-- The Yoneda-relative representability witness of a relatively ample morphism of algebraic
spaces. -/
abbrev relativelyRepresentableHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) [h : AlgebraicSpace.RelativelyAmple f L] :
    CategoryTheory.yoneda.relativelyRepresentable f :=
  h.representable

-- Local declaration justification (search instability): RelativelyAmple depends on
-- the morphism `f : X ⟶ Y`, which does not appear in `IsQuasicoherent L`.
set_option synthInstance.checkSynthOrder false in
/-- A relatively ample module on an algebraic space is quasi-coherent. -/
instance isQuasicoherent_of_relativelyAmple {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) [AlgebraicSpace.RelativelyAmple f L] :
    L.IsQuasicoherent :=
  sorry

/-- The morphism `ofOver U ⟶ T` classified by a point of the groupoid fibration associated to
`T`. -/
def SpaceOver.pointHom {T : AlgebraicSpace specZ} (x : (spaceStack T).total) :
    ofOver ((spaceStack T).p.obj x) ⟶ T :=
  yonedaEquiv.symm x.unop.2

/-- Yoneda maps of scheme-points commute with morphisms in the element category. -/
theorem SpaceOver.pointHom_naturality {T : AlgebraicSpace specZ}
    {x y : (spaceStack T).total} (φ : x ⟶ y) :
    yoneda.map ((spaceStack T).p.map φ) ≫ SpaceOver.pointHom y = SpaceOver.pointHom x := by
  apply yonedaEquiv.injective
  simp only [SpaceOver.pointHom, Equiv.apply_symm_apply]
  change T.functorOfPoints.map φ.unop.val y.unop.2 = x.unop.2
  exact φ.unop.property

/-- The representing scheme over `U` of the fibre of `f` at a scheme-point of `T`. -/
def SpaceOver.pointOver {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.RelativelyAmple f L] (x : (spaceStack T).total) : Over specZ :=
  (relativelyRepresentableHom f L).pullback (SpaceOver.pointHom x)

/-- The algebraic-space projection of the representing fibre to `X`. -/
def SpaceOver.pointFst {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.RelativelyAmple f L] (x : (spaceStack T).total) :
    ofOver (SpaceOver.pointOver f L x) ⟶ X :=
  (relativelyRepresentableHom f L).fst (SpaceOver.pointHom x)

/-- The structure morphism of the representing fibre, as a morphism of schemes over `Spec ℤ`. -/
def SpaceOver.pointSnd {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.RelativelyAmple f L] (x : (spaceStack T).total) :
    SpaceOver.pointOver f L x ⟶ (spaceStack T).p.obj x :=
  (relativelyRepresentableHom f L).snd (SpaceOver.pointHom x)

/-- The structure morphism `X_U ⟶ U` of the representing fibre. -/
def SpaceOver.pointSchemeHom {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.RelativelyAmple f L] (x : (spaceStack T).total) :
    (SpaceOver.pointOver f L x).left ⟶ ((spaceStack T).p.obj x).left :=
  (SpaceOver.pointSnd f L x).left

/-- The restriction of the pulled-back line bundle to the representing scheme `X_U`. -/
def SpaceOver.pointLine {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.RelativelyAmple f L] (x : (spaceStack T).total) :
    (SpaceOver.pointOver f L x).left.Modules :=
  (AlgebraicSpace.Modules.restrictToScheme (SpaceOver.pointOver f L x)).obj
    ((AlgebraicSpace.Modules.pullback (SpaceOver.pointFst f L x)).obj L)

/-- The representing scheme morphism `X_U ⟶ U` is proper. -/
instance SpaceOver.instIsProper_pointSchemeHom {T X : AlgebraicSpace specZ} (f : X ⟶ T)
    (L : X.Modules) [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f]
    [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f] [AlgebraicSpace.RelativelyAmple f L]
    (x : (spaceStack T).total) : IsProper (SpaceOver.pointSchemeHom f L x) :=
  sorry

/-- The representing scheme morphism `X_U ⟶ U` is flat. -/
instance SpaceOver.instFlat_pointSchemeHom {T X : AlgebraicSpace specZ} (f : X ⟶ T)
    (L : X.Modules) [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f]
    [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f] [AlgebraicSpace.RelativelyAmple f L]
    (x : (spaceStack T).total) : AlgebraicGeometry.Flat (SpaceOver.pointSchemeHom f L x) :=
  sorry

/-- The representing scheme morphism `X_U ⟶ U` is of finite presentation. -/
instance SpaceOver.instFinitePresentation_pointSchemeHom {T X : AlgebraicSpace specZ}
    (f : X ⟶ T) (L : X.Modules) [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f]
    [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f] [AlgebraicSpace.RelativelyAmple f L]
    (x : (spaceStack T).total) :
    Scheme.Hom.FinitePresentation (SpaceOver.pointSchemeHom f L x) :=
  sorry

/-- The restricted line bundle is relatively ample on `X_U ⟶ U`. -/
instance SpaceOver.instRelativelyAmple_pointSchemeHom {T X : AlgebraicSpace specZ}
    (f : X ⟶ T) (L : X.Modules) [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f]
    [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f] [AlgebraicSpace.RelativelyAmple f L]
    (x : (spaceStack T).total) :
    RelativelyAmple (SpaceOver.pointSchemeHom f L x) (SpaceOver.pointLine f L x) :=
  sorry

/-- The Polarized object `(X_U ⟶ U, L|_U)`. -/
def SpaceOver.pointObj {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f] [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f]
    [AlgebraicSpace.RelativelyAmple f L] (x : (spaceStack T).total) : Obj :=
  Polarized.of (SpaceOver.pointSchemeHom f L x) (SpaceOver.pointLine f L x)

/-- Over-commutativity of fibre comparison. -/
theorem SpaceOver.pointMapOver_w {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.RelativelyAmple f L] {x y : (spaceStack T).total} (φ : x ⟶ y) :
    SpaceOver.pointFst f L x ≫ f =
      CategoryTheory.yoneda.map (SpaceOver.pointSnd f L x ≫ (spaceStack T).p.map φ) ≫
        SpaceOver.pointHom y := by
  change (relativelyRepresentableHom f L).fst (SpaceOver.pointHom x) ≫ f = _
  rw [(relativelyRepresentableHom f L).w]
  rw [yoneda.map_comp, Category.assoc, SpaceOver.pointHom_naturality]
  rfl

/-- The morphism `X_U ⟶ X_V` of representing schemes over `U ⟶ V`. -/
def SpaceOver.pointMapOver {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.RelativelyAmple f L] {x y : (spaceStack T).total} (φ : x ⟶ y) :
    SpaceOver.pointOver f L x ⟶ SpaceOver.pointOver f L y :=
  (relativelyRepresentableHom f L).lift (SpaceOver.pointFst f L x)
    (SpaceOver.pointSnd f L x ≫ (spaceStack T).p.map φ) (SpaceOver.pointMapOver_w f L φ)

/-- Pulling the restricted line bundle of `X_V` back along `X_U ⟶ X_V` recovers the restricted
line bundle of `X_U`. -/
def SpaceOver.pointMapIso {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.RelativelyAmple f L] {x y : (spaceStack T).total} (φ : x ⟶ y) :
    (Scheme.Modules.pullback (SpaceOver.pointMapOver f L φ).left).obj (SpaceOver.pointLine f L y) ≅
      SpaceOver.pointLine f L x :=
  compositePullbackIso (SpaceOver.pointFst f L y) (SpaceOver.pointMapOver f L φ) L ≪≫
    eqToIso
      (congrArg
        (fun k ↦
          (AlgebraicSpace.Modules.restrictToScheme (SpaceOver.pointOver f L x)).obj
            ((AlgebraicSpace.Modules.pullback k).obj L))
        ((relativelyRepresentableHom f L).lift_fst (SpaceOver.pointFst f L x)
          (SpaceOver.pointSnd f L x ≫ (spaceStack T).p.map φ) (SpaceOver.pointMapOver_w f L φ)))

/-- The cartesian square of representing scheme morphisms along a morphism of scheme-points of
`T`. -/
theorem SpaceOver.pointMap_isPullback {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f] [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f]
    [AlgebraicSpace.RelativelyAmple f L] {x y : (spaceStack T).total} (φ : x ⟶ y) :
    IsPullback (SpaceOver.pointMapOver f L φ).left (SpaceOver.pointSchemeHom f L x)
      (SpaceOver.pointSchemeHom f L y) ((spaceStack T).p.map φ).left :=
  (CategoryTheory.Functor.relativelyRepresentable.ChangeOfBase.isPullback (relativelyRepresentableHom f L)
    (SpaceOver.pointHom x) (SpaceOver.pointHom y) ((spaceStack T).p.map φ)
    (SpaceOver.pointHom_naturality φ)).map (Over.forget specZ)

/-- The morphism of polarized schemes `X_U ⟶ X_V` over `U ⟶ V`. -/
def SpaceOver.pointMap {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f] [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f]
    [AlgebraicSpace.RelativelyAmple f L] {x y : (spaceStack T).total} (φ : x ⟶ y) :
    SpaceOver.pointObj f L x ⟶ SpaceOver.pointObj f L y :=
  Polarized.homMk (SpaceOver.pointMapOver f L φ).left ((spaceStack T).p.map φ).left
    (SpaceOver.pointMap_isPullback f L φ) (SpaceOver.pointMapIso f L φ)

/-- Identity morphisms of scheme-points act as identities on `X_U`. -/
theorem SpaceOver.pointMap_id {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f] [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f]
    [AlgebraicSpace.RelativelyAmple f L] (x : (spaceStack T).total) :
    SpaceOver.pointMap f L (𝟙 x) = 𝟙 (SpaceOver.pointObj f L x) :=
  sorry

/-- Base change of a polarized family along scheme-points of `T` preserves composition. -/
theorem SpaceOver.pointMap_comp {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f] [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f]
    [AlgebraicSpace.RelativelyAmple f L] {x y z : (spaceStack T).total} (φ : x ⟶ y) (ψ : y ⟶ z) :
    SpaceOver.pointMap f L (φ ≫ ψ) = SpaceOver.pointMap f L φ ≫ SpaceOver.pointMap f L ψ :=
  sorry

/-- The total functor sending a scheme-point of `T` to the polarized scheme `X_U ⟶ U`. -/
def SpaceOver.baseChangeFunctor {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f] [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f]
    [AlgebraicSpace.RelativelyAmple f L] : (spaceStack T).total ⥤ Obj where
  obj := SpaceOver.pointObj f L
  map := SpaceOver.pointMap f L
  map_id := SpaceOver.pointMap_id f L
  map_comp := SpaceOver.pointMap_comp f L

/-- The based functor `SpaceOver.baseChange f L` lies over `(Sch / Spec ℤ)_fppf`. -/
theorem SpaceOver.baseChange_w {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f] [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f]
    [AlgebraicSpace.RelativelyAmple f L] :
    SpaceOver.baseChangeFunctor f L ⋙ overSpecZ.p = (spaceStack T).p :=
  sorry

/-- Base change of a polarized algebraic-space family `(X ⟶ T, L)` along scheme-points of `T`
is a based functor `S_T ⥤ᵇ Polarized`. -/
def SpaceOver.baseChange {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f] [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f]
    [AlgebraicSpace.RelativelyAmple f L] :
    (spaceStack T).toBasedCategory ⥤ᵇ overSpecZ where
  toFunctor := SpaceOver.baseChangeFunctor f L
  w := SpaceOver.baseChange_w f L

/-- The underlying functor of `SpaceOver.baseChange f L` is `SpaceOver.baseChangeFunctor f L`. -/
theorem SpaceOver.baseChange_toFunctor {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f] [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f]
    [AlgebraicSpace.RelativelyAmple f L] :
    (SpaceOver.baseChange f L).toFunctor = SpaceOver.baseChangeFunctor f L :=
  rfl

/-- `SpaceOver.baseChange f L` sends a point `x` to `SpaceOver.pointObj f L x`. -/
theorem SpaceOver.baseChange_obj {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f] [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f]
    [AlgebraicSpace.RelativelyAmple f L] (x : (spaceStack T).total) :
    (SpaceOver.baseChange f L).obj x = SpaceOver.pointObj f L x :=
  rfl

/-- The two legs of the fibrewise comparison of representing fibres along a morphism of
polarized families over `T` agree over `T`. -/
theorem SpaceOver.yonedaAppOver_w {T : AlgebraicSpace specZ} {P Q : SpaceOver T}
    (α : P ⟶ Q) (x : (spaceStack T).total) :
    SpaceOver.pointFst P.hom P.line x ≫ α.map ≫ Q.hom =
      CategoryTheory.yoneda.map (SpaceOver.pointSnd P.hom P.line x) ≫ SpaceOver.pointHom x :=
  (congrArg (fun k ↦ SpaceOver.pointFst P.hom P.line x ≫ k) α.w).trans
    ((relativelyRepresentableHom P.hom P.line).w (SpaceOver.pointHom x))

/-- The morphism `X_U ⟶ Y_U` of representing schemes induced by a morphism of polarized
families over `T`. -/
def SpaceOver.yonedaAppOver {T : AlgebraicSpace specZ} {P Q : SpaceOver T} (α : P ⟶ Q)
    (x : (spaceStack T).total) :
    SpaceOver.pointOver P.hom P.line x ⟶ SpaceOver.pointOver Q.hom Q.line x :=
  (relativelyRepresentableHom Q.hom Q.line).lift
    (SpaceOver.pointFst P.hom P.line x ≫ α.map) (SpaceOver.pointSnd P.hom P.line x)
    (SpaceOver.yonedaAppOver_w α x)

/-- Pulling `Y_U`'s restricted line bundle back along `X_U ⟶ Y_U` recovers `X_U`'s restricted
line bundle, via the line-bundle isomorphism of `α`. -/
def SpaceOver.yonedaAppIso {T : AlgebraicSpace specZ} {P Q : SpaceOver T} (α : P ⟶ Q)
    (x : (spaceStack T).total) :
    (Scheme.Modules.pullback (SpaceOver.yonedaAppOver α x).left).obj
      (SpaceOver.pointLine Q.hom Q.line x) ≅ SpaceOver.pointLine P.hom P.line x :=
  compositePullbackIso (SpaceOver.pointFst Q.hom Q.line x) (SpaceOver.yonedaAppOver α x) Q.line ≪≫
    eqToIso
      (congrArg
        (fun k ↦
          (AlgebraicSpace.Modules.restrictToScheme (SpaceOver.pointOver P.hom P.line x)).obj
            ((AlgebraicSpace.Modules.pullback k).obj Q.line))
        ((relativelyRepresentableHom Q.hom Q.line).lift_fst
          (SpaceOver.pointFst P.hom P.line x ≫ α.map) (SpaceOver.pointSnd P.hom P.line x)
          (SpaceOver.yonedaAppOver_w α x))) ≪≫
    (AlgebraicSpace.Modules.restrictToScheme (SpaceOver.pointOver P.hom P.line x)).mapIso
      ((AlgebraicSpace.Modules.pullbackCompIso (SpaceOver.pointFst P.hom P.line x) α.map).symm.app
        Q.line) ≪≫
    (AlgebraicSpace.Modules.restrictToScheme (SpaceOver.pointOver P.hom P.line x)).mapIso
      ((AlgebraicSpace.Modules.pullback (SpaceOver.pointFst P.hom P.line x)).mapIso α.iso)

/-- The cartesian square of fibrewise representing scheme morphisms along a morphism of
polarized families over `T`. -/
theorem SpaceOver.yonedaApp_isPullback {T : AlgebraicSpace specZ} {P Q : SpaceOver T}
    (α : P ⟶ Q) (x : (spaceStack T).total) :
    IsPullback (SpaceOver.yonedaAppOver α x).left (SpaceOver.pointSchemeHom P.hom P.line x)
      (SpaceOver.pointSchemeHom Q.hom Q.line x) (𝟙 ((spaceStack T).p.obj x).left) := by
  let e := SpaceOver.Hom.isoLeft α
  let e' : P.X.functorOfPoints ≅ Q.X.functorOfPoints :=
    { hom := e.hom, inv := e.inv, hom_inv_id := e.hom_inv_id, inv_hom_id := e.inv_hom_id }
  -- Local instance justification (proof-local temporary data): ChangeOfSource.isPullback uses the underlying presheaf isomorphism constructed from α.
  letI : @IsIso ((Over specZ)ᵒᵖ ⥤ Type _) _ P.X.functorOfPoints Q.X.functorOfPoints α.map :=
    e'.isIso_hom
  exact (CategoryTheory.Functor.relativelyRepresentable.ChangeOfSource.isPullback P.hom Q.hom
    (relativelyRepresentableHom P.hom P.line) (relativelyRepresentableHom Q.hom Q.line)
    α.map α.w (SpaceOver.pointHom x)).map (Over.forget specZ)

/-- The component at a scheme-point of `T` of the based natural transformation associated to a
morphism of polarized families over `T`. -/
def SpaceOver.yonedaApp {T : AlgebraicSpace specZ} {P Q : SpaceOver T} (α : P ⟶ Q)
    (x : (spaceStack T).total) :
    (SpaceOver.baseChange P.hom P.line).obj x ⟶ (SpaceOver.baseChange Q.hom Q.line).obj x :=
  Polarized.homMk (SpaceOver.yonedaAppOver α x).left
    (𝟙 ((spaceStack T).p.obj x).left) (SpaceOver.yonedaApp_isPullback α x)
    (SpaceOver.yonedaAppIso α x)

/-- Components of `SpaceOver.yonedaApp` are natural in scheme-points of `T`. -/
theorem SpaceOver.yonedaApp_naturality {T : AlgebraicSpace specZ} {P Q : SpaceOver T}
    (α : P ⟶ Q) ⦃x y : (spaceStack T).total⦄ (φ : x ⟶ y) :
    (SpaceOver.baseChange P.hom P.line).map φ ≫ SpaceOver.yonedaApp α y =
      SpaceOver.yonedaApp α x ≫ (SpaceOver.baseChange Q.hom Q.line).map φ :=
  sorry

/-- Fibrewise comparison morphisms lift identities of the base. -/
theorem SpaceOver.yonedaApp_isHomLift {T : AlgebraicSpace specZ} {P Q : SpaceOver T}
    (α : P ⟶ Q) (x : (spaceStack T).total) :
    overSpecZ.p.IsHomLift (𝟙 ((spaceStack T).p.obj x)) (SpaceOver.yonedaApp α x) :=
  sorry

/-- The based natural transformation induced by a morphism of polarized families over `T`. -/
def SpaceOver.yonedaMap {T : AlgebraicSpace specZ} {P Q : SpaceOver T} (α : P ⟶ Q) :
    SpaceOver.baseChange P.hom P.line ⟶ SpaceOver.baseChange Q.hom Q.line where
  app := SpaceOver.yonedaApp α
  naturality := SpaceOver.yonedaApp_naturality α
  isHomLift' := SpaceOver.yonedaApp_isHomLift α

/-- Identity morphisms of `SpaceOver T` act as identity based natural transformations. -/
theorem SpaceOver.yonedaMap_id {T : AlgebraicSpace specZ} (P : SpaceOver T) :
    SpaceOver.yonedaMap (𝟙 P) = 𝟙 (SpaceOver.baseChange P.hom P.line) :=
  sorry

/-- `SpaceOver.yonedaMap` preserves composition in `SpaceOver T`. -/
theorem SpaceOver.yonedaMap_comp {T : AlgebraicSpace specZ} {P Q R : SpaceOver T}
    (α : P ⟶ Q) (β : Q ⟶ R) :
    SpaceOver.yonedaMap (α ≫ β) = SpaceOver.yonedaMap α ≫ SpaceOver.yonedaMap β :=
  sorry

/-- The comparison functor sending a polarized algebraic-space family `(X ⟶ T, L)` to the
based functor `U / T ↦ (X_U ⟶ U, L|_U)`. -/
def SpaceOver.yoneda (T : AlgebraicSpace specZ) :
    SpaceOver T ⥤ ((spaceStack T).toBasedCategory ⥤ᵇ overSpecZ) where
  obj P := SpaceOver.baseChange P.hom P.line
  map := SpaceOver.yonedaMap
  map_id := SpaceOver.yonedaMap_id
  map_comp := SpaceOver.yonedaMap_comp

/-- `SpaceOver.yoneda` sends `SpaceOver.of f L` to `SpaceOver.baseChange f L`. -/
theorem SpaceOver.yoneda_obj {T X : AlgebraicSpace specZ} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f] [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f]
    [AlgebraicSpace.RelativelyAmple f L] :
    (SpaceOver.yoneda T).obj (SpaceOver.of f L) = SpaceOver.baseChange f L :=
  rfl

/-- The forward functor of polarized families over `T` is an equivalence of categories. -/
instance SpaceOver.yoneda.instIsEquivalence (T : AlgebraicSpace specZ) :
    (SpaceOver.yoneda T).IsEquivalence :=
  sorry

end AlgebraicGeometry.Polarized
