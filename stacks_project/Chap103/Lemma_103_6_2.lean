module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import stacks_project.Chap96.Lemma_96_12_3_Pullback
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact

/-!
# Locally quasi-coherent higher direct images on algebraic stacks

Along a quasi-compact and quasi-separated morphism of algebraic stacks, étale
higher direct images of locally quasi-coherent modules remain locally
quasi-coherent.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The total functor is cocontinuous for the topologies of the étale ringed sites. -/
instance toFunctor_etaleRinged_isCocontinuous {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).IsCocontinuous
      (etaleRingedSite X).siteTopology (etaleRingedSite Y).siteTopology :=
  CartesianBasedFunctor.inheritedTopology.isCocontinuous
    (toCartesianBasedFunctor f) (StandardTopology.etale.overTopology S)

/-- Étale ringed sites admit type-valued sheafification in universe `u`. -/
instance etaleRingedSite_hasSheafify_type (X : GroupoidsOver S) :
    HasSheafify (etaleRingedSite X).siteTopology (Type u) :=
  sorry

/-- Ring-valued sheaves on the étale ringed site compose with `forget RingCat`. -/
instance etaleRingedSite_hasSheafCompose_forget_ring (X : GroupoidsOver S) :
    (etaleRingedSite X).siteTopology.HasSheafCompose (forget RingCat.{u}) :=
  sorry

/-- Pointwise right Kan extensions exist for type-valued presheaves along the total
functor of a 1-morphism. -/
instance toFunctor_op_hasPointwiseRightKanExtension_type {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    ∀ P : (etaleRingedSite X).carrierᵒᵖ ⥤ Type u,
      (toFunctor f).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Inverse of `etaleStructureSheafMap f`, as a morphism `f⁻¹ 𝒪_Y ⟶ 𝒪_X` of étale
ring sheaves. -/
def etaleStructureSheafMap_inv {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (etaleStructureSheaf Y) ⟶
      etaleStructureSheaf X :=
  @CategoryTheory.inv _ _ _ _ (etaleStructureSheafMap f) (etaleStructureSheafMap_isIso f)

/-- `etaleStructureSheafMap_inv f` is the inverse of `etaleStructureSheafMap f`. -/
theorem etaleStructureSheafMap_inv_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    etaleStructureSheafMap_inv f =
      @CategoryTheory.inv _ _ _ _ (etaleStructureSheafMap f)
        (etaleStructureSheafMap_isIso f) :=
  sorry

/-- Underlying presheaf of `etaleStructureSheafMap_inv`, as a map
`(toFunctor f).op ⋙ 𝒪_Y ⟶ 𝒪_X`. -/
def etaleStructureSheafMap_inv_presheaf {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).op ⋙ (etaleRingedSite Y).structureSheaf.obj ⟶
      (etaleRingedSite X).structureSheaf.obj :=
  ((toFunctor f).sheafPushforwardContinuousCompSheafToPresheafIso
      RingCat.{u} X.etaleTopology Y.etaleTopology).symm.hom.app
    (etaleStructureSheaf Y) ≫ (etaleStructureSheafMap_inv f).hom

/-- `etaleStructureSheafMap_inv_presheaf` is the presheaf of
`etaleStructureSheafMap_inv` after the continuous-pushforward identification. -/
theorem etaleStructureSheafMap_inv_presheaf_eq {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    etaleStructureSheafMap_inv_presheaf f =
      ((toFunctor f).sheafPushforwardContinuousCompSheafToPresheafIso
          RingCat.{u} X.etaleTopology Y.etaleTopology).symm.hom.app
        (etaleStructureSheaf Y) ≫ (etaleStructureSheafMap_inv f).hom :=
  sorry

/-- The morphism of étale ringed topoi induced by a 1-morphism, with structure map
the inverse of `etaleStructureSheafMap`. -/
def moduleDirectImageToposHom {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    RingedSite.ToposHom (etaleRingedSite X) (etaleRingedSite Y) :=
  @RingedSite.Cocontinuous.toRingedTopos.{u + 1, u, u + 1, u, u}
    (etaleRingedSite X) (etaleRingedSite Y) (toFunctor f)
    (toFunctor_etaleRinged_isCocontinuous f)
    (etaleRingedSite_hasSheafify_type X)
    (toFunctor_op_hasPointwiseRightKanExtension_type f)
    (etaleRingedSite_hasSheafCompose_forget_ring X)
    (etaleRingedSite_hasSheafCompose_forget_ring Y)
    (etaleStructureSheafMap_inv_presheaf f)

/-- `moduleDirectImageToposHom f` is the cocontinuous ringed-topos morphism with
structure map the inverse of `etaleStructureSheafMap f`. -/
theorem moduleDirectImageToposHom_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    moduleDirectImageToposHom f =
      @RingedSite.Cocontinuous.toRingedTopos.{u + 1, u, u + 1, u, u}
        (etaleRingedSite X) (etaleRingedSite Y) (toFunctor f)
        (toFunctor_etaleRinged_isCocontinuous f)
        (etaleRingedSite_hasSheafify_type X)
        (toFunctor_op_hasPointwiseRightKanExtension_type f)
        (etaleRingedSite_hasSheafCompose_forget_ring X)
        (etaleRingedSite_hasSheafCompose_forget_ring Y)
        (etaleStructureSheafMap_inv_presheaf f) :=
  sorry

/-- Direct image `f_*` of étale `𝒪`-modules along a 1-morphism, on the commutative
étale ringed site, with structure map the inverse of `etaleStructureSheafMap`. -/
def moduleDirectImage {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    etaleModules X ⥤ etaleModules Y :=
  (moduleDirectImageToposHom f).modulePushforward

/-- `moduleDirectImage f` is module pushforward of `moduleDirectImageToposHom f`. -/
theorem moduleDirectImage_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    moduleDirectImage f = (moduleDirectImageToposHom f).modulePushforward :=
  sorry

/-- Étale module direct image is additive. -/
instance moduleDirectImage_additive {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (moduleDirectImage f).Additive :=
  RingedSite.ToposHom.modulePushforward_additive (moduleDirectImageToposHom f)

/-- Étale modules on a category fibred in groupoids admit injective resolutions. -/
instance instHasInjectiveResolutions_etaleModules (X : GroupoidsOver S) :
    HasInjectiveResolutions (etaleModules X) :=
  sorry

/-- The degree-`i` étale higher direct image functor `R^i f_*` on étale modules. -/
abbrev moduleHigherDirectImageFunctor {X Y : GroupoidsOver S} (f : X ⟶ Y) (i : ℕ) :
    etaleModules X ⥤ etaleModules Y :=
  (moduleDirectImage f).rightDerived i

/-- `moduleHigherDirectImageFunctor f i` is the degree-`i` right derived functor of
étale module direct image. -/
theorem moduleHigherDirectImageFunctor_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) (i : ℕ) :
    moduleHigherDirectImageFunctor f i = (moduleDirectImage f).rightDerived i :=
  sorry

/-- The degree-`i` étale higher direct image `R^i f_* F`. -/
abbrev moduleHigherDirectImage {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (F : etaleModules X) (i : ℕ) : etaleModules Y :=
  (moduleHigherDirectImageFunctor f i).obj F

/-- `moduleHigherDirectImage f F i` is the object map of `moduleHigherDirectImageFunctor`. -/
theorem moduleHigherDirectImage_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (F : etaleModules X) (i : ℕ) :
    moduleHigherDirectImage f F i = (moduleHigherDirectImageFunctor f i).obj F :=
  sorry

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Lemma 103.6.2: if `f : X ⟶ Y` is a quasi-compact and quasi-separated morphism
of algebraic stacks and `F` is a locally quasi-coherent étale `𝒪_X`-module,
then the étale higher direct image `R^i f_* F`, computed in the étale topology
on `GroupoidsOver.etaleModules`, is locally quasi-coherent on `Y_étale`. -/
@[stacks 075Z]
instance isLocallyQuasiCoherent_higherDirectImage
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (F : GroupoidsOver.etaleModules X) [IsLocallyQuasiCoherent F] (i : ℕ) :
    IsLocallyQuasiCoherent (GroupoidsOver.moduleHigherDirectImage f F i) :=
  sorry

/-- Explicit-hypothesis form of étale higher direct images preserving local
quasi-coherence along a quasi-compact quasi-separated morphism of algebraic
stacks. -/
theorem isLocallyQuasiCoherent_higherDirectImage_of
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {F : GroupoidsOver.etaleModules X} (hF : IsLocallyQuasiCoherent F) (i : ℕ) :
    IsLocallyQuasiCoherent (GroupoidsOver.moduleHigherDirectImage f F i) :=
  sorry

/-- Object-property form: étale `R^i f_*` sends locally quasi-coherent modules
on `X` into locally quasi-coherent modules on `Y`. -/
theorem mapsHigherDirectImage_locallyQuasiCoherent
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (i : ℕ) :
    locallyQuasiCoherent X ≤
      (locallyQuasiCoherent Y).inverseImage
        (GroupoidsOver.moduleHigherDirectImageFunctor f i) :=
  sorry

end AlgebraicGeometry.AlgebraicStack

