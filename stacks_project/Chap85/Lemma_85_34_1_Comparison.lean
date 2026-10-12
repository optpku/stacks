/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Square
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap73.Remark_73_4_14_StructureSheaf
public import stacks_project.Chap85.Lemma_85_33_1_Comparison
public import stacks_project.Chap85.Lemma_85_34_1_Ringed

/-!
# Fppf–étale comparison square of ringed topoi

The unringed square of Lemma 85.33.1 upgrades to a commutative square of
ringed topoi, with structure sheaves `𝒪_big,total`, `𝒪_U`, `𝒪_big`, and `𝒪_X`.
The left vertical arrow is the Section 85.22/85.21 slice-augmentation; the
right vertical arrow is the Section 85.32 étale augmentation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Fppf
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory.SimplicialObject
open RingedSite RingedSite.ToposHom
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))

/-- Sheaves of types in universe `u` on the total spaces-étale site admit sheafification. -/
instance hasSheafify_spacesEtaleTotalTopology_type :
    HasSheafify (spacesEtaleTotalTopology U) (Type u) :=
  sorry

/-- Sheaves of types in universe `u` on `(Spaces/U)_{fppf,total}` admit sheafification. -/
instance hasSheafify_sliceTotalTopology_fppf_type :
    HasSheafify (sliceTotalTopology (fppfTopology S) U) (Type u) :=
  sorry

/-- Opposite of `toSliceTotal U` admits left Kan extensions of type-valued presheaves
in universe `u`. -/
instance toSliceTotal_op_hasLeftKanExtension_type
    (P : (SpacesEtale U)ᵒᵖ ⥤ Type u) :
    (toSliceTotal U).op.HasLeftKanExtension P :=
  sorry

/-- Sheaf pullback along `toSliceTotal U` preserves finite limits on sheaves of types
in universe `u`. -/
instance toSliceTotal_sheafPullback_preservesFiniteLimits_type :
    PreservesFiniteLimits
      ((toSliceTotal U).sheafPullback (Type u)
        (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U)) :=
  sorry

/-- Coefficient-forgetful comparison for continuous pushforward along `toSliceTotal`. -/
def toSliceTotal_forgetIso :
    (toSliceTotal U).sheafPushforwardContinuous RingCat.{u}
          (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U) ⋙
        sheafCompose (spacesEtaleTotalTopology U) (forget RingCat.{u}) ≅
      sheafCompose (sliceTotalTopology (fppfTopology S) U) (forget RingCat.{u}) ⋙
        (toSliceTotal U).sheafPushforwardContinuous (Type u)
          (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U) :=
  eqToIso
    (Functor.sheafPushforwardContinuous.compSheafCompose (toSliceTotal U)
      (forget RingCat.{u}) (spacesEtaleTotalTopology U)
      (sliceTotalTopology (fppfTopology S) U))

/-- Direct-image structure map of `h`: identity on the common global-sections sheaf,
using that `toSliceTotal` is identity-on-objects. -/
def fppfEtaleRingedComparison_structureSheafMap :
    (etaleTotalRingedSite U).structureSheaf ⟶
      ((toSliceTotal U).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U)).obj
        (fppfTotalRingedSite U).structureSheaf :=
  CategoryTheory.ObjectProperty.homMk
    { app := fun Y ↦
        eqToHom
          ((etaleTotalStructureSheaf_obj U Y.unop).trans
            (fppfTotalStructureSheaf_obj U ((toSliceTotal U).obj Y.unop)).symm)
      naturality := fun _ _ _ ↦ sorry }

/-- Ring-compatibility of the identity-on-objects comparison `h`. -/
theorem fppfEtaleRingedComparison_isRingCompatible :
    @Direct.IsRingCompatible (fppfTotalRingedSite U) (etaleTotalRingedSite U) _ _
      ((toSliceTotal U).morphismOfTopoiInOfContinuous.{u, u + 1, u + 1, u + 1, u + 1}
        (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U))
      ((toSliceTotal U).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U))
      (toSliceTotal_forgetIso U) (fppfEtaleRingedComparison_structureSheafMap U) :=
  sorry

/-- The top horizontal morphism of ringed topoi
`h : (Sh((Spaces/U)_{fppf,total}), 𝒪_big,total) ⟶ (Sh(U_spaces,étale), 𝒪_U)`,
presented by `toSliceTotal`. -/
def fppfEtaleRingedComparison :
    ToposHom (fppfTotalRingedSite U) (etaleTotalRingedSite U) :=
  @ofDirectImage (fppfTotalRingedSite U) (etaleTotalRingedSite U) _ _
    ((toSliceTotal U).morphismOfTopoiInOfContinuous.{u, u + 1, u + 1, u + 1, u + 1}
      (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U))
    ((toSliceTotal U).sheafPushforwardContinuous RingCat.{u}
      (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U))
    (toSliceTotal_forgetIso U) (fppfEtaleRingedComparison_structureSheafMap U)
    (fppfEtaleRingedComparison_isRingCompatible U)

/-- The underlying topos morphism of `h` is presented by `toSliceTotal`. -/
theorem fppfEtaleRingedComparison_toTopos :
    (fppfEtaleRingedComparison U).toTopos =
      (toSliceTotal U).morphismOfTopoiInOfContinuous.{u, u + 1, u + 1, u + 1, u + 1}
        (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U) :=
  rfl

/-- Direct image of `h` is continuous sheaf pushforward along `toSliceTotal`. -/
theorem fppfEtaleRingedComparison_pushforward :
    (fppfEtaleRingedComparison U).toTopos.pushforward =
      (toSliceTotal U).sheafPushforwardContinuous (Type u)
        (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U) :=
  rfl

variable (X : AlgebraicSpace S)

/-- Sheaves of types in universe `u` on `(Spaces/X)_fppf` admit sheafification. -/
instance hasSheafify_overFppfTopology_type :
    HasSheafify (overFppfTopology X) (Type u) :=
  sorry

/-- Opposite of `spacesEtaleToBig X` admits left Kan extensions of type-valued
presheaves in universe `u`. -/
instance spacesEtaleToBig_op_hasLeftKanExtension_fppf_type
    (P : (spacesEtaleSite X)ᵒᵖ ⥤ Type u) :
    (spacesEtaleToBig X).op.HasLeftKanExtension P :=
  sorry

/-- Sheaf pullback along `spacesEtaleToBig X` into the big fppf topos preserves
finite limits on sheaves of types in universe `u`. -/
instance spacesEtaleToBig_sheafPullback_preservesFiniteLimits_fppf_type :
    PreservesFiniteLimits
      ((spacesEtaleToBig X).sheafPullback (Type u)
        (spacesEtaleTopology X) (overFppfTopology X)) :=
  sorry

/-- Coefficient-forgetful comparison for continuous pushforward along `spacesEtaleToBig`. -/
def spacesEtaleToBig_forgetIso :
    (spacesEtaleToBig X).sheafPushforwardContinuous RingCat.{u}
          (spacesEtaleTopology X) (overFppfTopology X) ⋙
        sheafCompose (spacesEtaleTopology X) (forget RingCat.{u}) ≅
      sheafCompose (overFppfTopology X) (forget RingCat.{u}) ⋙
        (spacesEtaleToBig X).sheafPushforwardContinuous (Type u)
          (spacesEtaleTopology X) (overFppfTopology X) :=
  eqToIso
    (Functor.sheafPushforwardContinuous.compSheafCompose (spacesEtaleToBig X)
      (forget RingCat.{u}) (spacesEtaleTopology X) (overFppfTopology X))

/-- `gamma Z` is the global-sections ring of `Z`, viewed in `RingCat`. -/
theorem gamma_eq_globalSectionsRing (Z : AlgebraicSpace S) :
    Big.gamma Z = (forget₂ CommRingCat RingCat).obj (globalSectionsRing Z) :=
  sorry

/-- `Γ(V, 𝒪_V)` as `gamma` agrees with the big fppf structure sheaf at `V / X`. -/
theorem gamma_eq_overFppfStructureSheaf (V : spacesEtaleSite X) :
    Big.gamma V.left =
      (overFppfStructureSheaf X).obj.obj (op ((spacesEtaleToBig X).obj V)) :=
  sorry

/-- Direct-image structure map of `h₋₁`: the comparison `𝒪_X(V) ⟶ Γ(V, 𝒪_V)`. -/
def spacesFppfRingedComparison_structureSheafMap :
    (spacesRingedSite X).structureSheaf ⟶
      ((spacesEtaleToBig X).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology X) (overFppfTopology X)).obj
        (overFppfRingedSite X).structureSheaf :=
  CategoryTheory.ObjectProperty.homMk
    { app := fun V ↦
        Big.spacesStructureToGamma V.unop ≫
          eqToHom (gamma_eq_overFppfStructureSheaf X V.unop) ≫
            (Functor.sheafPushforwardContinuousObjObjIso (spacesEtaleToBig X) RingCat.{u}
              (overFppfStructureSheaf X) V.unop).inv
      naturality := fun _ _ _ ↦ sorry }

/-- Ring-compatibility of the spaces-étale form of `a_X`. -/
theorem spacesFppfRingedComparison_isRingCompatible :
    @Direct.IsRingCompatible (overFppfRingedSite X) (spacesRingedSite X) _ _
      ((spacesEtaleToBig X).morphismOfTopoiInOfContinuous.{u, u + 1, u + 1, u + 1, u + 1}
        (spacesEtaleTopology X) (overFppfTopology X))
      ((spacesEtaleToBig X).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology X) (overFppfTopology X))
      (spacesEtaleToBig_forgetIso X) (spacesFppfRingedComparison_structureSheafMap X) :=
  sorry

/-- The bottom horizontal morphism of ringed topoi
`h₋₁ : (Sh((Spaces/X)_fppf), 𝒪_big) ⟶ (Sh(X_spaces,étale), 𝒪_X)`,
the spaces-étale form of `a_X`. -/
def spacesFppfRingedComparison :
    ToposHom (overFppfRingedSite X) (spacesRingedSite X) :=
  @ofDirectImage (overFppfRingedSite X) (spacesRingedSite X) _ _
    ((spacesEtaleToBig X).morphismOfTopoiInOfContinuous.{u, u + 1, u + 1, u + 1, u + 1}
      (spacesEtaleTopology X) (overFppfTopology X))
    ((spacesEtaleToBig X).sheafPushforwardContinuous RingCat.{u}
      (spacesEtaleTopology X) (overFppfTopology X))
    (spacesEtaleToBig_forgetIso X) (spacesFppfRingedComparison_structureSheafMap X)
    (spacesFppfRingedComparison_isRingCompatible X)

/-- The underlying topos morphism of `h₋₁` is presented by `spacesEtaleToBig`. -/
theorem spacesFppfRingedComparison_toTopos :
    (spacesFppfRingedComparison X).toTopos =
      (spacesEtaleToBig X).morphismOfTopoiInOfContinuous.{u, u + 1, u + 1, u + 1, u + 1}
        (spacesEtaleTopology X) (overFppfTopology X) :=
  rfl

variable {X : AlgebraicSpace S} (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- Opposite of `sliceAugmentationPullback` admits left Kan extensions of type-valued
presheaves in universe `u`. -/
instance sliceAugmentationPullback_op_hasLeftKanExtension_fppf_type
    (P : (Over X)ᵒᵖ ⥤ Type u) :
    (sliceAugmentationPullback U a).op.HasLeftKanExtension P :=
  sorry

/-- Sheaf pullback along `sliceAugmentationPullback` preserves finite limits on sheaves
of types in universe `u`. -/
instance sliceAugmentationPullback_sheafPullback_preservesFiniteLimits_fppf_type :
    PreservesFiniteLimits
      ((sliceAugmentationPullback U a).sheafPullback (Type u)
        (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U)) :=
  sorry

/-- Opposite of `augmentationFunctor a` admits left Kan extensions of type-valued
presheaves in universe `u`. -/
instance augmentationFunctor_op_hasLeftKanExtension_type
    (P : (spacesEtaleSite X)ᵒᵖ ⥤ Type u) :
    (augmentationFunctor U a).op.HasLeftKanExtension P :=
  sorry

/-- Sheaf pullback along `augmentationFunctor a` preserves finite limits on sheaves of
types in universe `u`. -/
instance augmentationFunctor_sheafPullback_preservesFiniteLimits_type :
    PreservesFiniteLimits
      ((augmentationFunctor U a).sheafPullback (Type u)
        (spacesEtaleTopology X) (spacesEtaleTotalTopology U)) :=
  sorry

/-- Coefficient-forgetful comparison for continuous pushforward along
`sliceAugmentationPullback`. -/
def sliceAugmentationPullback_forgetIso :
    (sliceAugmentationPullback U a).sheafPushforwardContinuous RingCat.{u}
          (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U) ⋙
        sheafCompose (overFppfTopology X) (forget RingCat.{u}) ≅
      sheafCompose (sliceTotalTopology (fppfTopology S) U) (forget RingCat.{u}) ⋙
        (sliceAugmentationPullback U a).sheafPushforwardContinuous (Type u)
          (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U) :=
  eqToIso
    (Functor.sheafPushforwardContinuous.compSheafCompose (sliceAugmentationPullback U a)
      (forget RingCat.{u}) (overFppfTopology X)
      (sliceTotalTopology (fppfTopology S) U))

/-- Coefficient-forgetful comparison for continuous pushforward along
`augmentationFunctor`. -/
def augmentationFunctor_forgetIso :
    (augmentationFunctor U a).sheafPushforwardContinuous RingCat.{u}
          (spacesEtaleTopology X) (spacesEtaleTotalTopology U) ⋙
        sheafCompose (spacesEtaleTopology X) (forget RingCat.{u}) ≅
      sheafCompose (spacesEtaleTotalTopology U) (forget RingCat.{u}) ⋙
        (augmentationFunctor U a).sheafPushforwardContinuous (Type u)
          (spacesEtaleTopology X) (spacesEtaleTotalTopology U) :=
  eqToIso
    (Functor.sheafPushforwardContinuous.compSheafCompose (augmentationFunctor U a)
      (forget RingCat.{u}) (spacesEtaleTopology X) (spacesEtaleTotalTopology U))

/-- The projection `V ×_X U_0 ⟶ V` of the degree-zero pullback. -/
def augmentationPullbackFst (V : Over X) :
    pullback V.hom (a.app (op ⦋0⦌)) ⟶ V.left :=
  pullback.fst V.hom (a.app (op ⦋0⦌))

/-- The fibre of `sliceAugmentationPullback` is the fibre product with `U_0`. -/
theorem sliceAugmentationPullback_obj_fiber_left (V : Over X) :
    ((sliceAugmentationPullback U a).obj V).fiber.left =
      pullback V.hom (a.app (op ⦋0⦌)) :=
  rfl

/-- Direct-image structure map of `a_fppf`: restriction along the projection
`V ×_X U_0 ⟶ V`. -/
def fppfAugmentationRinged_structureSheafMap :
    (overFppfRingedSite X).structureSheaf ⟶
      ((sliceAugmentationPullback U a).sheafPushforwardContinuous RingCat.{u}
        (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U)).obj
        (fppfTotalRingedSite U).structureSheaf :=
  CategoryTheory.ObjectProperty.homMk
    { app := fun V ↦
        (forget₂ CommRingCat RingCat).map
            (globalSectionsRingMap (augmentationPullbackFst U a V.unop)) ≫
          eqToHom
            ((congrArg ((forget₂ CommRingCat RingCat).obj ∘ globalSectionsRing)
                (sliceAugmentationPullback_obj_fiber_left U a V.unop).symm).trans
              (fppfTotalStructureSheaf_obj U
                ((sliceAugmentationPullback U a).obj V.unop)).symm) ≫
            (Functor.sheafPushforwardContinuousObjObjIso (sliceAugmentationPullback U a)
              RingCat.{u} (fppfTotalStructureSheaf U) V.unop).inv
      naturality := fun _ _ _ ↦ sorry }

/-- Ring-compatibility of the fppf slice-augmentation. -/
theorem fppfAugmentationRinged_isRingCompatible :
    @Direct.IsRingCompatible (fppfTotalRingedSite U) (overFppfRingedSite X) _ _
      ((sliceAugmentationPullback U a).morphismOfTopoiInOfContinuous.{u, u + 1, u + 1, u + 1, u + 1}
        (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U))
      ((sliceAugmentationPullback U a).sheafPushforwardContinuous RingCat.{u}
        (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U))
      (sliceAugmentationPullback_forgetIso U a) (fppfAugmentationRinged_structureSheafMap U a) :=
  sorry

/-- The left vertical morphism of ringed topoi
`a_fppf : (Sh((Spaces/U)_{fppf,total}), 𝒪_big,total) ⟶ (Sh((Spaces/X)_fppf), 𝒪_big)`,
presented by `sliceAugmentationPullback`. -/
def fppfAugmentationRinged :
    ToposHom (fppfTotalRingedSite U) (overFppfRingedSite X) :=
  @ofDirectImage (fppfTotalRingedSite U) (overFppfRingedSite X) _ _
    ((sliceAugmentationPullback U a).morphismOfTopoiInOfContinuous.{u, u + 1, u + 1, u + 1, u + 1}
      (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U))
    ((sliceAugmentationPullback U a).sheafPushforwardContinuous RingCat.{u}
      (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U))
    (sliceAugmentationPullback_forgetIso U a) (fppfAugmentationRinged_structureSheafMap U a)
    (fppfAugmentationRinged_isRingCompatible U a)

/-- The underlying topos morphism of `a_fppf` is presented by `sliceAugmentationPullback`. -/
theorem fppfAugmentationRinged_toTopos :
    (fppfAugmentationRinged U a).toTopos =
      (sliceAugmentationPullback U a).morphismOfTopoiInOfContinuous.{u, u + 1, u + 1, u + 1, u + 1}
        (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U) :=
  rfl

/-- The fibre of `augmentationFunctor` is the fibre product with `U_0`. -/
theorem augmentationFunctor_obj_left (V : spacesEtaleSite X) :
    ((augmentationFunctor U a).obj V).obj.left = pullback V.hom (a.app (op ⦋0⦌)) :=
  rfl

/-- Direct-image structure map of the étale augmentation: `𝒪_X(V) ⟶ Γ(V ×_X U_0, 𝒪)`. -/
def spacesEtaleAugmentationRinged_structureSheafMap :
    (spacesRingedSite X).structureSheaf ⟶
      ((augmentationFunctor U a).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).obj
        (etaleTotalRingedSite U).structureSheaf :=
  CategoryTheory.ObjectProperty.homMk
    { app := fun V ↦
        Big.spacesStructureToGamma V.unop ≫
          eqToHom (gamma_eq_globalSectionsRing V.unop.left) ≫
          (forget₂ CommRingCat RingCat).map
            (globalSectionsRingMap (augmentationPullbackFst U a ((spacesEtaleToBig X).obj V.unop))) ≫
          eqToHom
            ((congrArg ((forget₂ CommRingCat RingCat).obj ∘ globalSectionsRing)
                (augmentationFunctor_obj_left U a V.unop).symm).trans
              (etaleTotalStructureSheaf_obj U ((augmentationFunctor U a).obj V.unop)).symm) ≫
            (Functor.sheafPushforwardContinuousObjObjIso (augmentationFunctor U a) RingCat.{u}
              (etaleTotalStructureSheaf U) V.unop).inv
      naturality := fun _ _ _ ↦ sorry }

/-- Ring-compatibility of the spaces-étale augmentation. -/
theorem spacesEtaleAugmentationRinged_isRingCompatible :
    @Direct.IsRingCompatible (etaleTotalRingedSite U) (spacesRingedSite X) _ _
      ((augmentationFunctor U a).morphismOfTopoiInOfContinuous.{u, u + 1, u + 1, u + 1, u + 1}
        (spacesEtaleTopology X) (spacesEtaleTotalTopology U))
      ((augmentationFunctor U a).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology X) (spacesEtaleTotalTopology U))
      (augmentationFunctor_forgetIso U a) (spacesEtaleAugmentationRinged_structureSheafMap U a) :=
  sorry

/-- The right vertical morphism of ringed topoi
`a : (Sh(U_spaces,étale), 𝒪_U) ⟶ (Sh(X_spaces,étale), 𝒪_X)`, presented by
`augmentationFunctor`. -/
def spacesEtaleAugmentationRinged :
    ToposHom (etaleTotalRingedSite U) (spacesRingedSite X) :=
  @ofDirectImage (etaleTotalRingedSite U) (spacesRingedSite X) _ _
    ((augmentationFunctor U a).morphismOfTopoiInOfContinuous.{u, u + 1, u + 1, u + 1, u + 1}
      (spacesEtaleTopology X) (spacesEtaleTotalTopology U))
    ((augmentationFunctor U a).sheafPushforwardContinuous RingCat.{u}
      (spacesEtaleTopology X) (spacesEtaleTotalTopology U))
    (augmentationFunctor_forgetIso U a) (spacesEtaleAugmentationRinged_structureSheafMap U a)
    (spacesEtaleAugmentationRinged_isRingCompatible U a)

/-- The underlying topos morphism of the étale augmentation is presented by
`augmentationFunctor`. -/
theorem spacesEtaleAugmentationRinged_toTopos :
    (spacesEtaleAugmentationRinged U a).toTopos =
      (augmentationFunctor U a).morphismOfTopoiInOfContinuous.{u, u + 1, u + 1, u + 1, u + 1}
        (spacesEtaleTopology X) (spacesEtaleTotalTopology U) :=
  rfl

/-- The two presenting composites are continuous, so the pushforward comparison along
`presentingCommSq` is defined. -/
def fppfEtaleRingedCommSq_homIso :
    (ToposHom.comp (fppfEtaleRingedComparison U)
          (spacesEtaleAugmentationRinged U a)).toTopos.pushforward ≅
      (ToposHom.comp (fppfAugmentationRinged U a)
          (spacesFppfRingedComparison X)).toTopos.pushforward :=
  Functor.sheafPushforwardContinuousIso (presentingCommSq U a) (Type u)
    (spacesEtaleTopology X) (sliceTotalTopology (fppfTopology S) U)

/-- Compatibility of `fppfEtaleRingedCommSq_homIso` with the structure-sheaf maps. -/
theorem fppfEtaleRingedCommSq_comm :
    (ToposHom.comp (fppfEtaleRingedComparison U)
            (spacesEtaleAugmentationRinged U a)).directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans
          (fppfEtaleRingedCommSq_homIso U a).hom).app
          (fppfTotalRingedSite U).structureSheaf =
      (ToposHom.comp (fppfAugmentationRinged U a)
          (spacesFppfRingedComparison X)).directStructureMap :=
  sorry

/-- The commutative square of ringed topoi of Lemma 85.34.1, with edges `h`, `a_fppf`,
`a`, and `h₋₁`. -/
def fppfEtaleRingedCommSq :
    ToposHom.CommSquare (fppfTotalRingedSite U) (etaleTotalRingedSite U)
      (overFppfRingedSite X) (spacesRingedSite X) where
  upper := fppfEtaleRingedComparison U
  left := fppfAugmentationRinged U a
  right := spacesEtaleAugmentationRinged U a
  lower := spacesFppfRingedComparison X
  cell :=
    { homIso := fppfEtaleRingedCommSq_homIso U a
      comm := fppfEtaleRingedCommSq_comm U a }

/-- The upper edge of `fppfEtaleRingedCommSq` is `h`. -/
theorem fppfEtaleRingedCommSq_upper :
    (fppfEtaleRingedCommSq U a).upper = fppfEtaleRingedComparison U :=
  rfl

/-- The left edge of `fppfEtaleRingedCommSq` is `a_fppf`. -/
theorem fppfEtaleRingedCommSq_left :
    (fppfEtaleRingedCommSq U a).left = fppfAugmentationRinged U a :=
  rfl

/-- The right edge of `fppfEtaleRingedCommSq` is the Section 85.32 étale augmentation. -/
theorem fppfEtaleRingedCommSq_right :
    (fppfEtaleRingedCommSq U a).right = spacesEtaleAugmentationRinged U a :=
  rfl

/-- The lower edge of `fppfEtaleRingedCommSq` is `h₋₁`, the spaces-étale form of `a_X`. -/
theorem fppfEtaleRingedCommSq_lower :
    (fppfEtaleRingedCommSq U a).lower = spacesFppfRingedComparison X :=
  rfl

/-- On degree `n`, `toSliceTotal` after `includeStage` is the spaces-étale form of
`a_{U_n}`. -/
theorem toSliceTotal_comp_includeStage (n : SimplexCategoryᵒᵖ) :
    @SpacesEtale.includeStage _ U n ⋙ toSliceTotal U =
      spacesEtaleToBig (U.obj n) ⋙ Grothendieck.ι (sliceDiagram U) n :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
