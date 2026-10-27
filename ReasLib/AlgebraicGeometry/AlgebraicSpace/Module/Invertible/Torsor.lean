/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Invertible.LaurentAlgebra
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.StructureModule.Carrier
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Symmetric
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Universal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.SectionTensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent

/-! # The multiplicative torsor of an invertible module -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConcreteCategory CategoryTheory.Functor
open CategoryTheory.MonoidalCategory.InvertiblePower
open Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.IdealSubobject
open SheafOfModules.RingedSite SheafOfModules.RingedSite.ModuleSheafification
open RingedSite.ToposHom IsLocalRing TopologicalSpace
open scoped DirectSum TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The canonical `G_m`-torsor of an invertible `𝒪_X`-module. -/
noncomputable def gmTorsor (L : X.Modules) [isInvertibleObject L] : AlgebraicSpace S :=
  relativeSpec (invertibleLaurentAlgebra L)

/-- The structure morphism `q : T ⟶ X` of the `G_m`-torsor of `L`. -/
noncomputable def gmTorsorπ (L : X.Modules) [isInvertibleObject L] : gmTorsor L ⟶ X :=
  relativeSpecπ (invertibleLaurentAlgebra L)

/-- The `G_m`-torsor is the relative spectrum of the tensor-power algebra. -/
theorem gmTorsor_def (L : X.Modules) [isInvertibleObject L] :
    gmTorsor L = relativeSpec (invertibleLaurentAlgebra L) :=
  rfl

/-- The structure morphism of the `G_m`-torsor is the relative-spectrum projection. -/
theorem gmTorsorπ_def (L : X.Modules) [isInvertibleObject L] :
    gmTorsorπ L = relativeSpecπ (invertibleLaurentAlgebra L) :=
  rfl

/-- The Laurent algebra maps to the structure sheaf of its own relative spectrum by the universal counit. -/
noncomputable def invertibleLaurentToPushforward (L : X.Modules) [isInvertibleObject L] :
    invertibleLaurentSheaf L ⟶
      (commRingPushforward (gmTorsorπ L)).obj (commStructureSheaf (gmTorsor L)) :=
  (relativeSpecUniversalAlgebraMap (invertibleLaurentAlgebra L)).right

/-- The commutative pushforward `q_* 𝒪_T`, regarded as an `𝒪_X`-module by restriction
of scalars along `q^♯`. -/
noncomputable def gmTorsorπ_commPushforwardModule (L : X.Modules)
    [isInvertibleObject L] : X.Modules :=
  ofComm
    ((restrictionAlong (commStructureSheafMap (gmTorsorπ L))).obj
      (unitModule (smallEtaleTopology X)
        ((commRingPushforward (gmTorsorπ L)).obj
          (commStructureSheaf (gmTorsor L)))))

/-- Component of the tautological comparison `⨁_n L^{⊗ n} ⟶ q_* 𝒪_T` at an étale
object, as a morphism of `𝒪_X`-modules. -/
noncomputable def gmTorsorπ_laurentToPushforwardApp (L : X.Modules)
    [isInvertibleObject L] (U : (smallEtaleSite X)ᵒᵖ) :
    (invertibleLaurentModule L).val.obj U ⟶
      (gmTorsorπ_commPushforwardModule L).val.obj U :=
  @ModuleCat.ofHom ((structureSheaf X).obj.obj U) _
    ((invertibleLaurentModule L).val.obj U)
    ((gmTorsorπ_commPushforwardModule L).val.obj U)
    ((invertibleLaurentModule L).val.obj U).isAddCommGroup
    ((invertibleLaurentModule L).val.obj U).isModule
    ((gmTorsorπ_commPushforwardModule L).val.obj U).isAddCommGroup
    ((gmTorsorπ_commPushforwardModule L).val.obj U).isModule
    { toFun := fun x =>
        ((InducedCategory.Hom.hom
            (invertibleLaurentToPushforward L)).app U).hom x
      map_add' := sorry
      map_smul' := sorry }

/-- Underlying module morphism of the tautological comparison `⨁_n L^{⊗ n} ⟶ q_* 𝒪_T`
in the commutative pushforward presentation. -/
noncomputable def gmTorsorπ_laurentToCommPushforward (L : X.Modules)
    [isInvertibleObject L] :
    invertibleLaurentModule L ⟶ gmTorsorπ_commPushforwardModule L where
  val :=
    { app := fun U => gmTorsorπ_laurentToPushforwardApp L U
      naturality := sorry }

/-- The structure module `𝒪_T` in the commutative étale presentation. -/
noncomputable def gmTorsorStructureModule (L : X.Modules)
    [isInvertibleObject L] : (gmTorsor L).Modules :=
  ofComm
    ((restrictionAlong (𝟙 (commStructureSheaf (gmTorsor L)))).obj
      (unitModule (smallEtaleTopology (gmTorsor L))
        (commStructureSheaf (gmTorsor L))))

/-- Type-valued comparison of the commutative pushforward unit with the module
pushforward of `gmTorsorStructureModule`. -/
noncomputable def gmTorsorπ_commPushforwardToModulePushforwardUnderlying
    (L : X.Modules) [isInvertibleObject L] :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
        (gmTorsorπ_commPushforwardModule L) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
        ((pushforward (gmTorsorπ L)).obj (gmTorsorStructureModule L)) :=
  ConormalAlgebra.restrictionUnitCarrierToForget (commStructureSheafMap (gmTorsorπ L)) ≫
    (commRingPushforwardForgetTypeIso (gmTorsorπ L)).hom.app
      (commStructureSheaf (gmTorsor L)) ≫
    (typePushforward (gmTorsorπ L)).map
      (ConormalAlgebra.forgetToRestrictionUnitCarrier (𝟙 (commStructureSheaf (gmTorsor L)))) ≫
    (ModulePushforward.forgetIso (ringedToposHom (gmTorsorπ L))).inv.app
      (gmTorsorStructureModule L)

/-- Module comparison `q_* 𝒪_T` from the commutative presentation to module
pushforward of `gmTorsorStructureModule`. -/
noncomputable def gmTorsorπ_commPushforwardToModulePushforward (L : X.Modules)
    [isInvertibleObject L] :
    gmTorsorπ_commPushforwardModule L ⟶
      (pushforward (gmTorsorπ L)).obj (gmTorsorStructureModule L) :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf X)
    (gmTorsorπ_commPushforwardToModulePushforwardUnderlying L)
    (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry)

/-- Underlying module morphism of the tautological comparison `⨁_n L^{⊗ n} ⟶ q_* 𝒪_T`. -/
noncomputable def gmTorsorπ_laurentToPushforward (L : X.Modules)
    [isInvertibleObject L] :
    invertibleLaurentModule L ⟶
      (pushforward (gmTorsorπ L)).obj (gmTorsorStructureModule L) :=
  gmTorsorπ_laurentToCommPushforward L ≫
    gmTorsorπ_commPushforwardToModulePushforward L

/-- Identify the commutative structure module of `T` with the tensor unit of
`T.Modules`. -/
noncomputable def gmTorsorStructureModuleToTensorUnit (L : X.Modules)
    [isInvertibleObject L] :
    gmTorsorStructureModule L ⟶ 𝟙_ (gmTorsor L).Modules :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf (gmTorsor L))
    (ConormalAlgebra.restrictionUnitCarrierToForget (𝟙 (commStructureSheaf (gmTorsor L))) ≫
      forgetToStructureUnitCarrier (gmTorsor L) ≫
      (Sheaf.InternalModule.ToInternal.underlying
          (structureSheaf (gmTorsor L))).map
        (structureModuleIsoTensorUnit (gmTorsor L)).hom)
    (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry)

/-- Reverse comparison of the commutative structure module of `T` with the
tensor unit of `T.Modules`. -/
noncomputable def tensorUnitToGmTorsorStructureModule (L : X.Modules)
    [isInvertibleObject L] :
    𝟙_ (gmTorsor L).Modules ⟶ gmTorsorStructureModule L :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf (gmTorsor L))
    ((Sheaf.InternalModule.ToInternal.underlying
          (structureSheaf (gmTorsor L))).map
        (structureModuleIsoTensorUnit (gmTorsor L)).inv ≫
      structureUnitCarrierToForget (gmTorsor L) ≫
      ConormalAlgebra.forgetToRestrictionUnitCarrier (𝟙 (commStructureSheaf (gmTorsor L))))
    (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry)

/-- Canonical isomorphism of the commutative structure module of `T` with the
tensor unit `𝒪_T`. -/
noncomputable def gmTorsorStructureModuleIsoTensorUnit (L : X.Modules)
    [isInvertibleObject L] :
    gmTorsorStructureModule L ≅ 𝟙_ (gmTorsor L).Modules where
  hom := gmTorsorStructureModuleToTensorUnit L
  inv := tensorUnitToGmTorsorStructureModule L
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `gmTorsorStructureModuleIsoTensorUnit` is the
structure-module comparison. -/
theorem gmTorsorStructureModuleIsoTensorUnit_hom (L : X.Modules)
    [isInvertibleObject L] :
    (gmTorsorStructureModuleIsoTensorUnit L).hom =
      gmTorsorStructureModuleToTensorUnit L :=
  rfl

/-- The inverse of `gmTorsorStructureModuleIsoTensorUnit` is the reverse
structure-module comparison. -/
theorem gmTorsorStructureModuleIsoTensorUnit_inv (L : X.Modules)
    [isInvertibleObject L] :
    (gmTorsorStructureModuleIsoTensorUnit L).inv =
      tensorUnitToGmTorsorStructureModule L :=
  rfl

/-- The adjunct of degree-one insertion, as a morphism `q^* L ⟶ 𝒪_T`. -/
noncomputable def gmTorsorTrivHom (L : X.Modules) [isInvertibleObject L] :
    (pullback (gmTorsorπ L)).obj L ⟶ gmTorsorStructureModule L :=
  ((pullbackPushforwardAdjunction (gmTorsorπ L)).homEquiv
      L (gmTorsorStructureModule L)).symm
    (degreeIncludeOne L ≫ gmTorsorπ_laurentToPushforward L)

/-- The adjunct of degree-minus-one insertion, as a morphism
`q^* L^{⊗ -1} ⟶ 𝒪_T`. -/
noncomputable def gmTorsorDegreeNegOneHom (L : X.Modules)
    [isInvertibleObject L] :
    (pullback (gmTorsorπ L)).obj (obj L (-1)) ⟶ gmTorsorStructureModule L :=
  ((pullbackPushforwardAdjunction (gmTorsorπ L)).homEquiv
      (obj L (-1)) (gmTorsorStructureModule L)).symm
    (degreeInclude L (-1) ≫ gmTorsorπ_laurentToPushforward L)

/-- The reverse comparison `𝒪_T ⟶ q^* L` obtained by pulling back the
evaluation coevaluation of `L^{⊗ -1}` and contracting the resulting tensor
factor against `gmTorsorDegreeNegOneHom`. -/
noncomputable def gmTorsorTrivInv (L : X.Modules) [isInvertibleObject L] :
    𝟙_ (gmTorsor L).Modules ⟶ (pullback (gmTorsorπ L)).obj L :=
  (PullbackTensor.unitIso (gmTorsorπ L)).inv ≫
    (pullback (gmTorsorπ L)).map (evaluationIso L).inv ≫
      RelativeProj.pullbackTensorOplax (gmTorsorπ L) L (obj L (-1)) ≫
        ((pullback (gmTorsorπ L)).obj L ◁
          (gmTorsorDegreeNegOneHom L ≫
            (gmTorsorStructureModuleIsoTensorUnit L).hom)) ≫
          (ρ_ ((pullback (gmTorsorπ L)).obj L)).hom

/-- The tautological trivialization `α : q^* L ≅ 𝒪_T`. -/
noncomputable def gmTorsorTriv (L : X.Modules) [isInvertibleObject L] :
    (pullback (gmTorsorπ L)).obj L ≅ 𝟙_ (gmTorsor L).Modules where
  hom := gmTorsorTrivHom L ≫ (gmTorsorStructureModuleIsoTensorUnit L).hom
  inv := gmTorsorTrivInv L
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `gmTorsorTriv` is the adjunct of degree-one insertion,
composed with the canonical identification of the commutative structure module
with `𝒪_T`. -/
theorem gmTorsorTriv_hom (L : X.Modules) [isInvertibleObject L] :
    (gmTorsorTriv L).hom =
      gmTorsorTrivHom L ≫ (gmTorsorStructureModuleIsoTensorUnit L).hom :=
  rfl

/-- The structure morphism of the `G_m`-torsor of an invertible module is
surjective. -/
instance instSurjective_gmTorsorπ (L : X.Modules) [isInvertibleObject L] :
    Surjective (gmTorsorπ L) :=
  sorry

/-- The structure morphism of the `G_m`-torsor of an invertible module is
smooth. -/
instance instSmooth_gmTorsorπ (L : X.Modules) [isInvertibleObject L] :
    Smooth (gmTorsorπ L) :=
  sorry

/-- The structure morphism of the `G_m`-torsor of an invertible module is affine. -/
instance instAffine_gmTorsorπ (L : X.Modules) [isInvertibleObject L] :
    Affine (gmTorsorπ L) :=
  instAffine_relativeSpecπ (invertibleLaurentAlgebra L)

/-- The structure morphism of the `G_m`-torsor of an invertible module has
relative dimension `1`. -/
instance instRelativeDimension_gmTorsorπ (L : X.Modules) [isInvertibleObject L] :
    RelativeDimension (gmTorsorπ L) 1 :=
  sorry

/-- The structure morphism of the `G_m`-torsor of an invertible module is flat. -/
instance instFlat_gmTorsorπ (L : X.Modules) [isInvertibleObject L] :
    Flat (gmTorsorπ L) :=
  sorry

/-- The structure morphism of the `G_m`-torsor of an invertible module is locally
of finite type. -/
instance instLocallyOfFiniteType_gmTorsorπ (L : X.Modules)
    [isInvertibleObject L] :
    LocallyOfFiniteType (gmTorsorπ L) :=
  sorry

/-- The structure morphism of the `G_m`-torsor of an invertible module is
quasi-separated. -/
instance instQuasiSeparated_gmTorsorπ (L : X.Modules) [isInvertibleObject L] :
    QuasiSeparated (gmTorsorπ L) :=
  sorry

/-- Composition of the `G_m`-torsor projection with a quasi-separated morphism
remains quasi-separated. -/
instance instQuasiSeparated_gmTorsorπ_comp {B : AlgebraicSpace S}
    (f : X ⟶ B) (L : X.Modules) [isInvertibleObject L] [QuasiSeparated f] :
    QuasiSeparated (gmTorsorπ L ≫ f) :=
  quasiSeparated_comp (gmTorsorπ L) f

/-- Composition of the `G_m`-torsor projection with a locally finite type
morphism remains locally of finite type. -/
instance instLocallyOfFiniteType_gmTorsorπ_comp {B : AlgebraicSpace S}
    (f : X ⟶ B) (L : X.Modules) [isInvertibleObject L]
    [LocallyOfFiniteType f] :
    LocallyOfFiniteType (gmTorsorπ L ≫ f) :=
  locallyOfFiniteType_comp (gmTorsorπ L) f

/-- Composition of the `G_m`-torsor projection with a flat morphism remains
flat. -/
instance instFlat_gmTorsorπ_comp {B : AlgebraicSpace S} (f : X ⟶ B)
    (L : X.Modules) [isInvertibleObject L] [Flat f] :
    Flat (gmTorsorπ L ≫ f) :=
  sorry

/-- The `G_m`-torsor of an invertible module on a decent algebraic space is
decent. -/
instance instIsDecent_gmTorsor (L : X.Modules) [isInvertibleObject L]
    [IsDecent X] : IsDecent (gmTorsor L) :=
  sorry

/-- Inverse image of an integral closed subspace along the `G_m`-torsor remains
integral. -/
theorem isIntegral_inverseImage_gmTorsorπ (L : X.Modules)
    [isInvertibleObject L] (Z : ClosedSubspace X) [IsIntegral Z.X] :
    IsIntegral (Z.inverseImageSubspace (gmTorsorπ L)).X := sorry

/-- An actual Laurent algebra map gives an underlying map into the direct image of the unit module. -/
noncomputable def laurentAlgebraToUnitUnderlying {Y : AlgebraicSpace S}
    (h : Y ⟶ X) (L : X.Modules) [isInvertibleObject L]
    (α : (invertibleLaurentAlgebra L).obj ⟶ Under.mk (commStructureSheafMap h)) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj (invertibleLaurentModule L) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
        ((pushforward h).obj (𝟙_ Y.Modules)) :=
  ConormalAlgebra.restrictionUnitCarrierToForget (invertibleLaurentStructureMap L) ≫
    ((sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u})) ⋙
      sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).map α.right ≫
    (commRingPushforwardForgetTypeIso h).hom.app (commStructureSheaf Y) ≫
    (typePushforward h).map
      (forgetToStructureUnitCarrier Y ≫
        (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).map
          (structureModuleIsoTensorUnit Y).hom) ≫
    (ModulePushforward.forgetIso (ringedToposHom h)).inv.app (𝟙_ Y.Modules)

/-- The module map carried by an actual Laurent algebra map. -/
noncomputable def laurentAlgebraToUnitPushforward {Y : AlgebraicSpace S}
    (h : Y ⟶ X) (L : X.Modules) [isInvertibleObject L]
    (α : (invertibleLaurentAlgebra L).obj ⟶ Under.mk (commStructureSheafMap h)) :
    invertibleLaurentModule L ⟶ (pushforward h).obj (𝟙_ Y.Modules) :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf X)
    (laurentAlgebraToUnitUnderlying h L α) (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry)

/-- Adjunction sends degree-one evaluation of an algebra map to its frame homomorphism. -/
noncomputable def laurentAlgebraFrameHom {Y : AlgebraicSpace S}
    (h : Y ⟶ X) (L : X.Modules) [isInvertibleObject L]
    (α : (invertibleLaurentAlgebra L).obj ⟶ Under.mk (commStructureSheafMap h)) :
    (pullback h).obj L ⟶ 𝟙_ Y.Modules :=
  ((pullbackPushforwardAdjunction h).homEquiv L (𝟙_ Y.Modules)).symm
    (degreeIncludeOne L ≫ laurentAlgebraToUnitPushforward h L α)

/-- Section values of actual algebra maps whose degree-one adjunct is the supplied frame. -/
def IsFrameClassifyingSection {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) (a : (invertibleLaurentSheaf L).obj.obj U)
    (s : ((commRingPushforward h).obj (commStructureSheaf Y)).obj.obj U) : Prop :=
  ∃ α : (invertibleLaurentAlgebra L).obj ⟶ Under.mk (commStructureSheafMap h),
    laurentAlgebraFrameHom h L α = frame.hom ∧
      ((InducedCategory.Hom.hom α.right).app U).hom a = s

/-- Evaluate a Laurent section at a representing algebra map when one exists, and return zero otherwise. -/
noncomputable def frameClassifyingSection {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) (a : (invertibleLaurentSheaf L).obj.obj U) :
    ((commRingPushforward h).obj (commStructureSheaf Y)).obj.obj U := by
  classical
  exact if hs : ∃ s, IsFrameClassifyingSection h L frame U a s then Classical.choose hs else 0

/-- Local Laurent evaluation at the actual frame glues uniquely, so its section family is in range. -/
theorem frameClassifyingSection_inRange {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) (a : (invertibleLaurentSheaf L).obj.obj U) :
    ∃ s, IsFrameClassifyingSection h L frame U a s := sorry

/-- The selected value is supplied by an actual algebra map with the specified degree-one frame. -/
theorem frameClassifyingSection_spec {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) (a : (invertibleLaurentSheaf L).obj.obj U) :
    IsFrameClassifyingSection h L frame U a (frameClassifyingSection h L frame U a) := by
  classical
  unfold frameClassifyingSection
  split_ifs with hs
  · exact Classical.choose_spec hs
  · exact False.elim (hs (frameClassifyingSection_inRange h L frame U a))

/-- Two evaluations represented by algebra maps with the same degree-one frame agree. -/
theorem frameClassifyingSection_unique {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) (a : (invertibleLaurentSheaf L).obj.obj U)
    (s t : ((commRingPushforward h).obj (commStructureSheaf Y)).obj.obj U)
    (hs : IsFrameClassifyingSection h L frame U a s)
    (ht : IsFrameClassifyingSection h L frame U a t) : s = t := sorry

/-- Evaluation of the selected section agrees with every algebra map inducing the supplied frame. -/
theorem frameClassifyingSection_of_map {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules)
    (α : (invertibleLaurentAlgebra L).obj ⟶ Under.mk (commStructureSheafMap h))
    (hα : laurentAlgebraFrameHom h L α = frame.hom)
    (U : (smallEtaleSite X)ᵒᵖ) (a : (invertibleLaurentSheaf L).obj.obj U) :
    frameClassifyingSection h L frame U a =
      ((InducedCategory.Hom.hom α.right).app U).hom a := sorry


/-- The section ring map classified by the supplied frame, evaluating every Laurent degree. -/
noncomputable def frameClassifyingRingHom {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (invertibleLaurentSheaf L).obj.obj U →+*
      ((commRingPushforward h).obj (commStructureSheaf Y)).obj.obj U where
  toFun := frameClassifyingSection h L frame U
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- A frame, rather than a base morphism alone, determines its Laurent algebra homomorphism. -/
noncomputable def invertibleLaurentClassifyingMap {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules) :
    (invertibleLaurentAlgebra L).obj ⟶ Under.mk (commStructureSheafMap h) :=
  Under.homMk
    ⟨{ app := fun U ↦ @CommRingCat.ofHom ((invertibleLaurentSheaf L).obj.obj U)
         (((commRingPushforward h).obj (commStructureSheaf Y)).obj.obj U)
         (inferInstanceAs (CommRing ((invertibleLaurentSheaf L).obj.obj U)))
         (inferInstanceAs (CommRing (((commRingPushforward h).obj (commStructureSheaf Y)).obj.obj U)))
         (frameClassifyingRingHom h L frame U)
       naturality := sorry }⟩ sorry

/-- Pull an actual frame back along a test morphism, retaining the canonical composition and unit comparisons. -/
noncomputable def pullbackFrame {Y Z : AlgebraicSpace S} (h : Y ⟶ X) (t : Z ⟶ Y)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules) :
    (pullback (t ≫ h)).obj L ≅ 𝟙_ Z.Modules :=
  (pullbackCompIso t h).symm.app L ≪≫ (pullback t).mapIso frame ≪≫ PullbackTensor.unitIso t

/-- The morphism to the torsor classified by an actual trivialization of the pulled-back line. -/
noncomputable def gmTorsorLift {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules) :
    Y ⟶ gmTorsor L where
  app T := TypeCat.ofHom fun y ↦
    let t : ofOver T.unop ⟶ Y := yonedaEquiv.symm y
    relativeSpectrumPairMk (t ≫ h)
      (invertibleLaurentClassifyingMap (t ≫ h) L (pullbackFrame h t L frame))
  naturality := sorry

/-- The lift classified by a frame lies over its given base morphism. -/
theorem gmTorsorLift_comp_π {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules) :
    gmTorsorLift h L frame ≫ gmTorsorπ L = h := sorry

/-- Pulling the tautological trivialization back along the classified lift recovers the frame. -/
theorem gmTorsorLift_triv {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules) :
    frame.hom =
      eqToHom (congrArg (fun f ↦ (pullback f).obj L)
        (gmTorsorLift_comp_π h L frame).symm) ≫
      (pullbackCompIso (gmTorsorLift h L frame) (gmTorsorπ L)).inv.app L ≫
      (pullback (gmTorsorLift h L frame)).map (gmTorsorTriv L).hom ≫
      (PullbackTensor.unitIso (gmTorsorLift h L frame)).hom := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
