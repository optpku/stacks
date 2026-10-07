module

public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import stacks_project.Chap96.Lemma_96_8_1_RingedSite

/-!
# Associated morphisms of ringed topoi

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` induces, on each
associated `τ`-site, the identification `f⁻¹ 𝒪_Y ≅ 𝒪_X` and the corresponding morphism
of ringed topoi `Sh(X_τ) ⟶ Sh(Y_τ)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor Opposite
open FiberedCategoryOver.Groupoids
open scoped Bicategory MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The total functor of a 1-morphism is a morphism of associated `τ`-sites. -/
instance toFunctor_isMorphismOfSites {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    IsMorphismOfSites (X.associatedTopology τ) (Y.associatedTopology τ) (toFunctor f) :=
  sorry

/-- The total functor of a 1-morphism is continuous for associated `τ`-topologies. -/
instance toFunctor_isContinuous {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    (toFunctor f).IsContinuous (X.associatedTopology τ) (Y.associatedTopology τ) :=
  (toFunctor_isMorphismOfSites f τ).toIsContinuous

/-- The composite `toFunctor f ⋙ Y.p` is continuous from `X_τ` to the big `τ`-site of `S`. -/
instance toFunctor_comp_p_isContinuous {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    (toFunctor f ⋙ Y.p).IsContinuous (X.associatedTopology τ) (τ.overTopology S) :=
  Functor.isContinuous_comp (toFunctor f) Y.p
    (X.associatedTopology τ) (Y.associatedTopology τ) (τ.overTopology S)

/-- The cartesian total functor is continuous for associated `τ`-topologies. -/
instance toCartesianBasedFunctor_isContinuous {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    (toCartesianBasedFunctor f).toFunctor.IsContinuous
      (X.associatedTopology τ) (Y.associatedTopology τ) :=
  CartesianBasedFunctor.inheritedTopology.isContinuous
    (toCartesianBasedFunctor f) (τ.overTopology S)

/-- The cartesian total functor is cocontinuous for associated `τ`-topologies. -/
instance toCartesianBasedFunctor_isCocontinuous {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    (toCartesianBasedFunctor f).toFunctor.IsCocontinuous
      (X.associatedTopology τ) (Y.associatedTopology τ) :=
  CartesianBasedFunctor.inheritedTopology.isCocontinuous
    (toCartesianBasedFunctor f) (τ.overTopology S)

/-- Ring-valued sheaves on an associated `τ`-topology compose with `forget RingCat`. -/
instance associatedTopology_hasSheafCompose (X : GroupoidsOver S) (τ : StandardTopology) :
    (X.associatedTopology τ).HasSheafCompose (forget RingCat.{u}) :=
  sorry

/-- Ring-valued sheaves on an associated `τ`-ringed site compose with `forget RingCat`. -/
instance associatedRingedSite_hasSheafCompose (X : GroupoidsOver S) (τ : StandardTopology) :
    (associatedRingedSite X τ).siteTopology.HasSheafCompose (forget RingCat.{u}) :=
  sorry

/-- The canonical identification `f⁻¹ 𝒪_Y ≅ 𝒪_X` of associated `τ`-structure sheaves,
obtained from the commuting triangle `toFunctor f ⋙ Y.p = X.p`. -/
def associatedStructureSheafInverseImageIso {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
        (X.associatedTopology τ) (Y.associatedTopology τ)).obj
      (associatedStructureSheaf Y τ) ≅ associatedStructureSheaf X τ :=
  (sheafPushforwardContinuousComp' (eqToIso (comm f)) RingCat.{u}
      (X.associatedTopology τ) (Y.associatedTopology τ) (τ.overTopology S)).app
    (StandardTopology.Big.structureSheaf τ S)

/-- `associatedStructureSheafInverseImageIso` is the continuous-pushforward comparison
along `comm f`. -/
theorem associatedStructureSheafInverseImageIso_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    associatedStructureSheafInverseImageIso f τ =
      (sheafPushforwardContinuousComp' (eqToIso (comm f)) RingCat.{u}
          (X.associatedTopology τ) (Y.associatedTopology τ) (τ.overTopology S)).app
        (StandardTopology.Big.structureSheaf τ S) :=
  sorry

/-- At an object `x` of `X`, the identification `f⁻¹ 𝒪_Y ≅ 𝒪_X` evaluates as
`𝒪_Y((toFunctor f).obj x) = 𝒪_X(x)`. -/
theorem associatedStructureSheafInverseImageIso_app {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) (x : X.total) :
    (associatedStructureSheaf Y τ).obj.obj (op ((toFunctor f).obj x)) =
      (associatedStructureSheaf X τ).obj.obj (op x) :=
  sorry

/-- The structure-sheaf map of `toFunctorSiteHom`, identifying `𝒪_X` with the
continuous inverse image of `𝒪_Y` along `toFunctor f`. -/
def toFunctorSiteHom_structureSheafMap {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    (associatedRingedSite X τ).structureSheaf ⟶
      ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
        (X.associatedTopology τ) (Y.associatedTopology τ)).obj
        (associatedRingedSite Y τ).structureSheaf :=
  (associatedStructureSheafInverseImageIso f τ).inv

/-- The morphism of associated `τ`-ringed sites induced by a 1-morphism of
categories fibred in groupoids, with underlying functor `toFunctor f`. -/
def toFunctorSiteHom {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology) :
    RingedSite.Hom (associatedRingedSite Y τ) (associatedRingedSite X τ) where
  base := toFunctor f
  isMorphismOfSites := toFunctor_isMorphismOfSites f τ
  structureSheafMap := toFunctorSiteHom_structureSheafMap f τ

/-- The base of `toFunctorSiteHom f τ` is `toFunctor f`. -/
theorem toFunctorSiteHom_base {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    (toFunctorSiteHom f τ).base = toFunctor f :=
  sorry

/-- The total functor is cocontinuous for the topologies of the associated `τ`-ringed
sites. -/
instance toFunctor_isCocontinuous {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    (toFunctor f).IsCocontinuous
      (associatedRingedSite X τ).siteTopology (associatedRingedSite Y τ).siteTopology :=
  sorry

/-- Associated `τ`-ringed sites admit type-valued sheafification in universe `u`. -/
instance associatedRingedSite_hasSheafify_type (X : GroupoidsOver S)
    (τ : StandardTopology) :
    HasSheafify (associatedRingedSite X τ).siteTopology (Type u) :=
  sorry

/-- Pointwise right Kan extensions exist for type-valued presheaves along the total
functor of a 1-morphism. -/
instance toFunctor_op_hasPointwiseRightKanExtension_type {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (τ : StandardTopology) :
    ∀ P : (associatedRingedSite X τ).carrierᵒᵖ ⥤ Type u,
      (toFunctor f).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions along `toFunctor f` on the total category. -/
instance toFunctor_op_hasPointwiseRightKanExtension_total {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    ∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P :=
  sorry

/-- The identification `f⁻¹ 𝒪_Y ≅ 𝒪_X` as a morphism of underlying ring presheaves. -/
def associatedStructureSheafInverseImagePresheafHom {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (τ : StandardTopology) :
    (toFunctor f).op ⋙ (associatedRingedSite Y τ).structureSheaf.obj ⟶
      (associatedRingedSite X τ).structureSheaf.obj :=
  (associatedStructureSheafInverseImageIso f τ).hom.hom

/-- `associatedStructureSheafInverseImagePresheafHom` is the underlying presheaf morphism
of `associatedStructureSheafInverseImageIso`. -/
theorem associatedStructureSheafInverseImagePresheafHom_eq {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (τ : StandardTopology) :
    associatedStructureSheafInverseImagePresheafHom f τ =
      (associatedStructureSheafInverseImageIso f τ).hom.hom :=
  sorry

/-- The morphism of associated `τ`-ringed topoi induced by a 1-morphism of
categories fibred in groupoids, using the identification `f⁻¹ 𝒪_Y ≅ 𝒪_X`. -/
def associatedRingedToposHom {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology) :
    RingedSite.ToposHom (associatedRingedSite X τ) (associatedRingedSite Y τ) :=
  @RingedSite.Cocontinuous.toRingedTopos.{u + 1, u, u + 1, u, u}
    (associatedRingedSite X τ) (associatedRingedSite Y τ) (toFunctor f)
    (toFunctor_isCocontinuous f τ) (associatedRingedSite_hasSheafify_type X τ)
    (toFunctor_op_hasPointwiseRightKanExtension_type f τ)
    (associatedRingedSite_hasSheafCompose X τ)
    (associatedRingedSite_hasSheafCompose Y τ)
    (associatedStructureSheafInverseImagePresheafHom f τ)

/-- The underlying morphism of topoi of `associatedRingedToposHom f τ` is the
cocontinuous morphism of topoi induced by `toFunctor f`. -/
theorem associatedRingedToposHom_toTopos {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    (associatedRingedToposHom f τ).toTopos =
      @RingedSite.Cocontinuous.toTopos.{u + 1, u, u + 1, u, u}
        (associatedRingedSite X τ) (associatedRingedSite Y τ) (toFunctor f)
        (toFunctor_isCocontinuous f τ) (associatedRingedSite_hasSheafify_type X τ)
        (toFunctor_op_hasPointwiseRightKanExtension_type f τ) :=
  sorry

/-- The inverse-image structure map of `associatedRingedToposHom` is induced by
`associatedStructureSheafInverseImageIso`. -/
theorem associatedRingedToposHom_structureMap {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    (associatedRingedToposHom f τ).structureMap =
      @RingedSite.Cocontinuous.structureMap.{u + 1, u, u + 1, u, u}
        (associatedRingedSite X τ) (associatedRingedSite Y τ) (toFunctor f)
        (toFunctor_isCocontinuous f τ) (associatedRingedSite_hasSheafify_type X τ)
        (toFunctor_op_hasPointwiseRightKanExtension_type f τ)
        (associatedRingedSite_hasSheafCompose X τ)
        (associatedRingedSite_hasSheafCompose Y τ)
        (associatedStructureSheafInverseImagePresheafHom f τ) :=
  sorry

/-- The inverse-image structure map of `associatedRingedToposHom f τ` is an
isomorphism, recording the identification `f⁻¹ 𝒪_Y ≅ 𝒪_X`. -/
instance associatedRingedToposHom_structureMap_isIso {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (τ : StandardTopology) :
    IsIso (associatedRingedToposHom f τ).structureMap :=
  sorry

end AlgebraicGeometry.GroupoidsOver
