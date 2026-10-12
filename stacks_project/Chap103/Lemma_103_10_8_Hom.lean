/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Logic.Small.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal
public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
public import stacks_project.Chap103.Lemma_103_10_1_Adjunction

/-!
# Internal Hom from a finitely presented module into a quasi-coherent module

On an algebraic stack, sheaf Hom from a finitely presented `𝒪_X`-module into a
quasi-coherent module may be computed in the étale or fppf module categories.
The common value lies in `LQCoh^{fbc}`, and `Q` of that value represents
`Hom(H ⊗ F, G)` on quasi-coherent `H`.

The associated fppf lift from Lemma 96.12.5 cannot be imported together with
`LQCohFbc.toQCoh` (duplicate `projection_isContinuous` from
`Lemma_96_8_1_RingedSite` and `Lemma_96_11_2_Pullback`). Étale sheaf Hom is
therefore computed on `commEtaleRingedSiteLift`, and fppf sheaf Hom is the
identity-on-Γ restriction of scalars of that étale sheaf Hom.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.MonoidalClosed CategoryTheory.ObjectProperty
  SheafOfModules SheafOfModules.RingedSite
  SheafOfModules.RingedSite.InternalHom
open scoped SheafOfModules.RingedSite TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Ring-to-abelian-group sheaf composition exists on every slice of the étale
ringed site. -/
instance hasSheafCompose_etaleRingedSite_over (X : GroupoidsOver S) :
    ∀ x, ((etaleRingedSite X).siteTopology.over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Weak sheafification of abelian groups exists on every slice of the étale
ringed site. -/
instance hasWeakSheafify_etaleRingedSite_over (X : GroupoidsOver S) :
    ∀ x, HasWeakSheafify ((etaleRingedSite X).siteTopology.over x)
      AddCommGrpCat.{u} :=
  sorry

/-- Sheafification equivalences on slices of the étale ringed site are the
locally bijective morphisms. -/
instance wEqualsLocallyBijective_etaleRingedSite_over (X : GroupoidsOver S) :
    ∀ x, ((etaleRingedSite X).siteTopology.over x).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  sorry

/-- Finite presentation is preserved by restriction from the fppf site to the
étale site. -/
instance restriction_isFinitePresentation {X : GroupoidsOver S}
    [AlgebraicStack X] (F : fppfModules X) [F.IsFinitePresentation] :
    ((restriction X).obj F).IsFinitePresentation :=
  sorry

/-- Restriction of a quasi-coherent module is locally quasi-coherent. -/
instance restriction_isLocallyQuasiCoherent {X : GroupoidsOver S}
    [AlgebraicStack X] (G : QCoh X) :
    IsLocallyQuasiCoherent ((restriction X).obj G.obj) :=
  sorry

/-- Restriction of a quasi-coherent module has the flat base change property. -/
instance restriction_hasFlatBaseChange {X : GroupoidsOver S} [AlgebraicStack X]
    (G : QCoh X) :
    HasFlatBaseChange ((restriction X).obj G.obj) :=
  sorry

/-- A function between universe-`u` `ModuleCat` objects, with linearity deferred. -/
def moduleCatOfFun {R : Type u} [Ring R] (src tgt : ModuleCat.{u} R)
    (f : src → tgt) : src ⟶ tgt :=
  ModuleCat.ofHom
    { toFun := f
      map_add' := sorry
      map_smul' := sorry }

/-- A function between universe-`u + 1` `ModuleCat` objects, with linearity
deferred. -/
def moduleCatOfFunSucc {R : Type (u + 1)} [Ring R]
    (src tgt : ModuleCat.{u + 1} R) (f : src → tgt) : src ⟶ tgt :=
  ModuleCat.ofHom
    { toFun := f
      map_add' := sorry
      map_smul' := sorry }

/-- Down-universe of a module in universe `u + 1` with `u`-small carrier. -/
def moduleCatDown (R : Type u) [Ring R] (N : ModuleCat.{u + 1} R)
    [Small.{u} N] : ModuleCat.{u} R :=
  ModuleCat.of R (Shrink.{u} (N : Type (u + 1)))

/-- Restriction of scalars preserves `Small.{u}`. -/
instance restrictScalars_small.{r, s} {R : Type r} {S : Type s} [Ring R]
    [Ring S] (f : R →+* S) (N : ModuleCat.{u + 1} S) [h : Small.{u} N] :
    Small.{u} ((ModuleCat.restrictScalars.{u + 1} f).obj N) :=
  h

/-- Universe lift of an étale `𝒪_X`-module to the commutative lifted étale
ringed site. -/
def etaleModuleUniverseLift {X : GroupoidsOver S} (F : etaleModules X) :
    RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X) where
  val :=
    { obj U :=
        (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).obj
          ((ModuleCat.uliftFunctor.{u + 1, u}
              ((etaleRingedSite X).structureSheaf.obj.obj U)).obj
            (F.val.obj U))
      map i :=
        (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).map
          ((ModuleCat.uliftFunctor.{u + 1, u}
              ((etaleRingedSite X).structureSheaf.obj.obj _)).map
            (F.val.map i))
      map_id := sorry
      map_comp := sorry }
  isSheaf := sorry

/-- Universe-`u` sections of a lift of a universe-`u` étale module are `u`-small. -/
instance etaleModuleUniverseLift_small {X : GroupoidsOver S} (F : etaleModules X)
    (U : X.totalᵒᵖ) :
    Small.{u} ((etaleModuleUniverseLift F).val.obj U) :=
  Small.mk' Equiv.ulift.{u + 1, u}

/-- Inverse of `etaleModuleUniverseLift` on one lifted module. -/
def fromEtaleModuleUniverseLift {X : GroupoidsOver S}
    (M : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X))
    [∀ U, Small.{u} (M.val.obj U)] : etaleModules X where
  val :=
    { obj U :=
        moduleCatDown ((commEtaleStructureSheaf X).obj.obj U)
          ((ModuleCat.restrictScalars
              (ULift.ringEquiv.{u, u + 1}.symm).toRingHom).obj
            (M.val.obj U))
      map {U V} i :=
        moduleCatOfFun _ _
          (fun x ↦
            equivShrink
              (((ModuleCat.restrictScalars
                    (ULift.ringEquiv.{u, u + 1}.symm).toRingHom).obj
                  (M.val.obj V)) : Type (u + 1))
              (((ModuleCat.restrictScalars
                    (ULift.ringEquiv.{u, u + 1}.symm).toRingHom).map
                  (M.val.map i)).hom
                ((equivShrink
                    (((ModuleCat.restrictScalars
                          (ULift.ringEquiv.{u, u + 1}.symm).toRingHom).obj
                        (M.val.obj U)) : Type (u + 1))).symm x)))
      map_id := sorry
      map_comp := sorry }
  isSheaf := sorry

/-- Down-transport of a morphism of universe-lifted étale modules. -/
def fromEtaleModuleUniverseLift_map {X : GroupoidsOver S}
    {M N : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)}
    [∀ U, Small.{u} (M.val.obj U)] [∀ U, Small.{u} (N.val.obj U)] (f : M ⟶ N) :
    fromEtaleModuleUniverseLift M ⟶ fromEtaleModuleUniverseLift N where
  val :=
    { app U :=
        moduleCatOfFun _ _
          (fun x ↦
            equivShrink
              (((ModuleCat.restrictScalars
                    (ULift.ringEquiv.{u, u + 1}.symm).toRingHom).obj
                  (N.val.obj U)) : Type (u + 1))
              (((ModuleCat.restrictScalars
                    (ULift.ringEquiv.{u, u + 1}.symm).toRingHom).map
                  (f.val.app U)).hom
                ((equivShrink
                    (((ModuleCat.restrictScalars
                          (ULift.ringEquiv.{u, u + 1}.symm).toRingHom).obj
                        (M.val.obj U)) : Type (u + 1))).symm x)))
      naturality := sorry }

/-- Universe lift of a morphism of étale modules. -/
def etaleModuleUniverseLift_map {X : GroupoidsOver S} {F G : etaleModules X}
    (f : F ⟶ G) : etaleModuleUniverseLift F ⟶ etaleModuleUniverseLift G where
  val :=
    { app U :=
        moduleCatOfFunSucc _ _
          (fun x ↦ ULift.up ((f.val.app U).hom (ULift.down x)))
      naturality := sorry }

/-- Forward component of the lift-down round trip. -/
def fromEtaleModuleUniverseLift_isoHomApp {X : GroupoidsOver S}
    (M : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X))
    [∀ U, Small.{u} (M.val.obj U)] (U : X.totalᵒᵖ) :
    (etaleModuleUniverseLift (fromEtaleModuleUniverseLift M)).val.obj U ⟶
      M.val.obj U :=
  moduleCatOfFunSucc _ _
    (fun x ↦ (equivShrink (M.val.obj U : Type (u + 1))).symm (ULift.down x))

/-- Inverse component of the lift-down round trip. -/
def fromEtaleModuleUniverseLift_isoInvApp {X : GroupoidsOver S}
    (M : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X))
    [∀ U, Small.{u} (M.val.obj U)] (U : X.totalᵒᵖ) :
    M.val.obj U ⟶
      (etaleModuleUniverseLift (fromEtaleModuleUniverseLift M)).val.obj U :=
  moduleCatOfFunSucc _ _
    (fun y ↦ ULift.up (equivShrink (M.val.obj U : Type (u + 1)) y))

/-- The lift of the down-transport of a lifted étale module is canonically
isomorphic to the original lifted module. -/
def fromEtaleModuleUniverseLift_iso {X : GroupoidsOver S}
    (M : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X))
    [∀ U, Small.{u} (M.val.obj U)] :
    etaleModuleUniverseLift (fromEtaleModuleUniverseLift M) ≅ M where
  hom :=
    { val :=
        { app := fromEtaleModuleUniverseLift_isoHomApp M
          naturality := sorry } }
  inv :=
    { val :=
        { app := fromEtaleModuleUniverseLift_isoInvApp M
          naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The down-transport of a universe lift of an étale module is canonically
isomorphic to the original module. -/
def etaleModuleUniverseLift_fromIso {X : GroupoidsOver S} (F : etaleModules X) :
    fromEtaleModuleUniverseLift (etaleModuleUniverseLift F) ≅ F where
  hom :=
    { val :=
        { app U :=
            moduleCatOfFun _ _
              (fun x ↦
                ULift.down
                  ((equivShrink
                      (((ModuleCat.restrictScalars
                            (ULift.ringEquiv.{u, u + 1}.symm).toRingHom).obj
                          ((etaleModuleUniverseLift F).val.obj U)) :
                        Type (u + 1))).symm x))
          naturality := sorry } }
  inv :=
    { val :=
        { app U :=
            moduleCatOfFun _ _
              (fun y ↦
                equivShrink
                  (((ModuleCat.restrictScalars
                        (ULift.ringEquiv.{u, u + 1}.symm).toRingHom).obj
                      ((etaleModuleUniverseLift F).val.obj U)) : Type (u + 1))
                  (ULift.up y))
          naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The canonical sheaf Hom of two étale modules, as internal Hom of universe
lifts. -/
def liftedEtaleInternalHom {X : GroupoidsOver S} (F G : etaleModules X) :
    RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X) :=
  SheafOfModules.RingedSite.InternalHom.obj.{u + 1, u, u}
    (commEtaleStructureSheafLift X)
    (etaleModuleUniverseLift F) (etaleModuleUniverseLift G)

/-- `liftedEtaleInternalHom` is the explicit local internal Hom of the universe
lifts. -/
theorem liftedEtaleInternalHom_eq {X : GroupoidsOver S} (F G : etaleModules X) :
    liftedEtaleInternalHom F G =
      SheafOfModules.RingedSite.InternalHom.obj.{u + 1, u, u}
        (commEtaleStructureSheafLift X)
        (etaleModuleUniverseLift F) (etaleModuleUniverseLift G) :=
  rfl

/-- Sections of lifted étale sheaf Hom from a finitely presented module are
`u`-small. -/
instance liftedEtaleInternalHom_small {X : GroupoidsOver S}
    (F G : etaleModules X) [F.IsFinitePresentation] (U : X.totalᵒᵖ) :
    Small.{u} ((liftedEtaleInternalHom F G).val.obj U) :=
  sorry

/-- The sheaf Hom `SheafHom_{𝒪_X}(F, G)` of étale `𝒪_X`-modules. -/
def moduleSheafHomOnEtale {X : GroupoidsOver S} (F G : etaleModules X)
    [F.IsFinitePresentation] : etaleModules X :=
  fromEtaleModuleUniverseLift (liftedEtaleInternalHom F G)

/-- `moduleSheafHomOnEtale` is the down-transport of `liftedEtaleInternalHom`. -/
theorem moduleSheafHomOnEtale_eq {X : GroupoidsOver S} (F G : etaleModules X)
    [F.IsFinitePresentation] :
    moduleSheafHomOnEtale F G =
      fromEtaleModuleUniverseLift (liftedEtaleInternalHom F G) :=
  rfl

/-- The universe lift of `moduleSheafHomOnEtale` is the lifted internal Hom. -/
def moduleSheafHomOnEtale_spec {X : GroupoidsOver S} (F G : etaleModules X)
    [F.IsFinitePresentation] :
    etaleModuleUniverseLift (moduleSheafHomOnEtale F G) ≅
      liftedEtaleInternalHom F G :=
  fromEtaleModuleUniverseLift_iso (liftedEtaleInternalHom F G)

/-- Sheaf Hom from a finitely presented étale module into a locally
quasi-coherent étale module is locally quasi-coherent. -/
instance isLocallyQuasiCoherent_moduleSheafHomOnEtale {X : GroupoidsOver S}
    (F G : etaleModules X) [F.IsFinitePresentation] [IsLocallyQuasiCoherent G] :
    IsLocallyQuasiCoherent (moduleSheafHomOnEtale F G) :=
  sorry

/-- Sheaf Hom from a finitely presented étale module into a module with the
flat base change property again has the flat base change property. -/
instance hasFlatBaseChange_moduleSheafHomOnEtale {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : etaleModules X) [F.IsFinitePresentation]
    [HasFlatBaseChange G] :
    HasFlatBaseChange (moduleSheafHomOnEtale F G) :=
  sorry

/-- Identity-on-Γ comparison of the fppf and étale structure presheaves. -/
def fppfToEtaleStructurePresheafHom (X : GroupoidsOver S) :
    (fppfRingedSite X).structureSheaf.obj ⟶
      (etaleRingedSite X).structureSheaf.obj where
  app U := 𝟙 _
  naturality := sorry

/-- The sheaf Hom `SheafHom_{𝒪_X}(F, G)` of fppf `𝒪_X`-modules, obtained by
identity-on-Γ restriction of scalars of étale sheaf Hom of the restrictions. -/
def moduleSheafHomFppf {X : GroupoidsOver S} [AlgebraicStack X]
    (F G : fppfModules X) [F.IsFinitePresentation] : fppfModules X where
  val :=
    (PresheafOfModules.restrictScalars (fppfToEtaleStructurePresheafHom X)).obj
      (moduleSheafHomOnEtale ((restriction X).obj F) ((restriction X).obj G)).val
  isSheaf := sorry

/-- `moduleSheafHomFppf` is identity-on-Γ restriction of scalars of étale sheaf Hom. -/
theorem moduleSheafHomFppf_eq {X : GroupoidsOver S} [AlgebraicStack X]
    (F G : fppfModules X) [F.IsFinitePresentation] :
    (moduleSheafHomFppf F G).val =
      (PresheafOfModules.restrictScalars (fppfToEtaleStructurePresheafHom X)).obj
        (moduleSheafHomOnEtale ((restriction X).obj F)
          ((restriction X).obj G)).val :=
  rfl

/-- Restriction of fppf sheaf Hom is the étale sheaf Hom of the restrictions,
via identity-on-Γ restriction of scalars. -/
def moduleSheafHom_restrictionIso {X : GroupoidsOver S} [AlgebraicStack X]
    (F G : fppfModules X) [F.IsFinitePresentation] :
    (restriction X).obj (moduleSheafHomFppf F G) ≅
      moduleSheafHomOnEtale ((restriction X).obj F) ((restriction X).obj G) where
  hom :=
    { val :=
        { app U := moduleCatOfFun _ _ id
          naturality := sorry } }
  inv :=
    { val :=
        { app U := moduleCatOfFun _ _ id
          naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The sheaf Hom of a finitely presented fppf module into a quasi-coherent
module, as an object of étale `LQCoh^{fbc}(𝒪_X)`. -/
def moduleSheafHomLQCohFbc {X : GroupoidsOver S} [AlgebraicStack X]
    (F : fppfModules X) (G : QCoh X) [F.IsFinitePresentation] : LQCohFbc X :=
  ⟨moduleSheafHomOnEtale ((restriction X).obj F) ((restriction X).obj G.obj),
    sorry⟩

/-- The underlying étale module of `moduleSheafHomLQCohFbc` is étale sheaf Hom. -/
theorem moduleSheafHomLQCohFbc_eq {X : GroupoidsOver S} [AlgebraicStack X]
    (F : fppfModules X) (G : QCoh X) [F.IsFinitePresentation] :
    (LQCohFbc.inclusion X).obj (moduleSheafHomLQCohFbc F G) =
      moduleSheafHomOnEtale ((restriction X).obj F)
        ((restriction X).obj G.obj) :=
  rfl

/-- The common sheaf Hom lies in `lqcohFbc`. -/
theorem moduleSheafHomOnEtale_mem_lqcohFbc {X : GroupoidsOver S}
    [AlgebraicStack X] (F : fppfModules X) (G : QCoh X)
    [F.IsFinitePresentation] :
    lqcohFbc X
      (moduleSheafHomOnEtale ((restriction X).obj F)
        ((restriction X).obj G.obj)) :=
  sorry

/-- Currying of lifted internal Hom, in source tensor order `H ⊗ F`. -/
def liftedEtaleInternalHom_homEquiv {X : GroupoidsOver S}
    (F G H : etaleModules X) :
    (etaleModuleUniverseLift H ⟶ liftedEtaleInternalHom F G) ≃
      (tensorObj (etaleModuleUniverseLift H) (etaleModuleUniverseLift F) ⟶
        etaleModuleUniverseLift G) :=
  (SheafOfModules.RingedSite.InternalHom.homEquiv
      (commEtaleStructureSheafLift X) (etaleModuleUniverseLift F)
      (etaleModuleUniverseLift H) (etaleModuleUniverseLift G)).symm.trans
    ((β_ (etaleModuleUniverseLift F) (etaleModuleUniverseLift H)).homCongr
      (Iso.refl (etaleModuleUniverseLift G)))

/-- Sheafification of the pointwise étale tensor, as an étale module. -/
def etalePointwiseTensorSheafify {X : GroupoidsOver S} (H F : etaleModules X) :
    etaleModules X :=
  (moduleSheafification.{u + 1, u, u, u} (commEtaleStructureSheaf X)).obj
    (PresheafOfModules.Monoidal.tensorObj H.val F.val)

/-- Pure tensor of étale sections, as a section of the sheafified pointwise tensor. -/
def etalePointwiseTensorSection {X : GroupoidsOver S} {H F : etaleModules X}
    (U : X.totalᵒᵖ) (x : H.val.obj U) (y : F.val.obj U) :
    (etalePointwiseTensorSheafify H F).val.obj U :=
  (moduleSheafificationUnitToVal.{u + 1, u, u, u} (commEtaleStructureSheaf X)
      (PresheafOfModules.Monoidal.tensorObj H.val F.val)).app U (x ⊗ₜ y)

/-- Comparison from the sheafified pointwise tensor to `moduleTensorEtale`. -/
def etalePointwiseTensorSheafify_iso {X : GroupoidsOver S}
    (H F : etaleModules X) :
    etalePointwiseTensorSheafify H F ≅ moduleTensorEtale H F :=
  (Functor.Monoidal.μIso
      (moduleSheafification.{u + 1, u, u, u} (commEtaleStructureSheaf X))
      H.val F.val).symm ≪≫
    tensorIso
      (moduleSheafificationValIso.{u + 1, u, u, u}
        (commEtaleStructureSheaf X) H)
      (moduleSheafificationValIso.{u + 1, u, u, u}
        (commEtaleStructureSheaf X) F)

/-- Comparison from the tensor of universe lifts to the lift of the étale
tensor product, by `ULift.up` of the sheafification unit on pure tensors. -/
def etaleModuleUniverseLift_tensorHom {X : GroupoidsOver S}
    (H F : etaleModules X) :
    tensorObj (etaleModuleUniverseLift H) (etaleModuleUniverseLift F) ⟶
      etaleModuleUniverseLift (moduleTensorEtale H F) :=
  SectionBilinearMap.hom.{u + 1, u}
    { app U :=
        LinearMap.mk₂ ((commEtaleStructureSheafLift X).obj.obj U)
          (fun x y ↦
            ULift.up
              ((etalePointwiseTensorSheafify_iso H F).hom.val.app U
                (etalePointwiseTensorSection U (ULift.down x) (ULift.down y))))
          sorry sorry sorry sorry
      naturality := sorry }

/-- Morphisms out of the tensor of universe lifts correspond to morphisms of
étale tensors: evaluate the lifted bilinear map on `ULift` of étale sections,
and conversely precompose with `etaleModuleUniverseLift_tensorHom`. -/
def etaleModuleUniverseLift_tensorHomEquiv {X : GroupoidsOver S}
    (H F G : etaleModules X) :
    (tensorObj (etaleModuleUniverseLift H) (etaleModuleUniverseLift F) ⟶
      etaleModuleUniverseLift G) ≃
      (moduleTensorEtale H F ⟶ G) where
  toFun f :=
    (etalePointwiseTensorSheafify_iso H F).inv ≫
      (moduleSheafificationHomEquiv.{u + 1, u, u, u}
          (commEtaleStructureSheaf X)
          (PresheafOfModules.Monoidal.tensorObj H.val F.val) G).symm
        (PresheafOfModules.BilinearMap.toHom
          { app U :=
              LinearMap.mk₂ ((commEtaleStructureSheaf X).obj.obj U)
                (fun x y ↦
                  ULift.down
                    ((SectionBilinearMap.ofHom f).app U
                      (ULift.up x : (etaleModuleUniverseLift H).val.obj U)
                      (ULift.up y : (etaleModuleUniverseLift F).val.obj U)))
                sorry sorry sorry sorry
            naturality := sorry })
  invFun g :=
    etaleModuleUniverseLift_tensorHom H F ≫ etaleModuleUniverseLift_map g
  left_inv := sorry
  right_inv := sorry

/-- The reverse map of `etaleModuleUniverseLift_tensorHomEquiv` is precomposition
with the bilinear comparison of universe lifts. -/
theorem etaleModuleUniverseLift_tensorHomEquiv_apply {X : GroupoidsOver S}
    (H F G : etaleModules X) (g : moduleTensorEtale H F ⟶ G) :
    (etaleModuleUniverseLift_tensorHomEquiv H F G).symm g =
      etaleModuleUniverseLift_tensorHom H F ≫ etaleModuleUniverseLift_map g :=
  rfl

/-- Hom-sets of étale modules are equivalent to Hom-sets of their universe
lifts. -/
def etaleModuleUniverseLift_homEquiv {X : GroupoidsOver S}
    (F G : etaleModules X) :
    (F ⟶ G) ≃
      (etaleModuleUniverseLift F ⟶ etaleModuleUniverseLift G) where
  toFun := etaleModuleUniverseLift_map
  invFun f :=
    (etaleModuleUniverseLift_fromIso F).inv ≫
      fromEtaleModuleUniverseLift_map f ≫
        (etaleModuleUniverseLift_fromIso G).hom
  left_inv := sorry
  right_inv := sorry

/-- Tensor/internal-Hom equivalence for étale sheaf Hom from a finitely presented
module. -/
def moduleSheafHomOnEtale_homEquiv {X : GroupoidsOver S}
    (F G H : etaleModules X) [F.IsFinitePresentation] :
    (H ⟶ moduleSheafHomOnEtale F G) ≃
      (moduleTensorEtale H F ⟶ G) :=
  ((etaleModuleUniverseLift_homEquiv H (moduleSheafHomOnEtale F G)).trans
      ((Iso.refl (etaleModuleUniverseLift H)).homCongr
        (moduleSheafHomOnEtale_spec F G))).trans
    ((liftedEtaleInternalHom_homEquiv F G H).trans
      (etaleModuleUniverseLift_tensorHomEquiv H F G))

namespace QCoh

/-- The quasi-coherent internal Hom `hom(F, G) = Q(SheafHom_{𝒪_X}(F, G))` from a
finitely presented module into a quasi-coherent module. -/
def internalHomFP {X : GroupoidsOver S} [AlgebraicStack X] (F : fppfModules X)
    (G : QCoh X) [F.IsFinitePresentation] : QCoh X :=
  (LQCohFbc.toQCoh X).obj (moduleSheafHomLQCohFbc F G)

/-- `internalHomFP` is `Q` of the `LQCoh^{fbc}` sheaf Hom. -/
theorem internalHomFP_eq {X : GroupoidsOver S} [AlgebraicStack X]
    (F : fppfModules X) (G : QCoh X) [F.IsFinitePresentation] :
    internalHomFP F G =
      (LQCohFbc.toQCoh X).obj (moduleSheafHomLQCohFbc F G) :=
  rfl

/-- The universal property
`Hom_X(H, hom(F, G)) = Hom_X(H ⊗_{𝒪_X} F, G)` for quasi-coherent `H`, obtained
from the adjunction `toLQCohFbc ⊣ toQCoh`, full faithfulness of `LQCoh^{fbc}`,
and the étale tensor/internal-Hom equivalence. -/
def internalHomFP_homEquiv {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F : fppfModules X)
    (G H : QCoh X) [F.IsFinitePresentation] :
    (H ⟶ internalHomFP F G) ≃
      (moduleTensorEtale ((restriction X).obj H.obj) ((restriction X).obj F) ⟶
        (restriction X).obj G.obj) :=
  ((adj.homEquiv H (moduleSheafHomLQCohFbc F G)).symm.trans
      ((lqcohFbc X).fullyFaithfulι.homEquiv)).trans
    (moduleSheafHomOnEtale_homEquiv ((restriction X).obj F)
      ((restriction X).obj G.obj) ((restriction X).obj H.obj))

/-- `internalHomFP_homEquiv` is the composite of `adj.homEquiv`, the
`LQCoh^{fbc}` inclusion, and étale currying. -/
theorem internalHomFP_homEquiv_eq {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F : fppfModules X)
    (G H : QCoh X) [F.IsFinitePresentation] :
    internalHomFP_homEquiv adj F G H =
      ((adj.homEquiv H (moduleSheafHomLQCohFbc F G)).symm.trans
          ((lqcohFbc X).fullyFaithfulι.homEquiv)).trans
        (moduleSheafHomOnEtale_homEquiv ((restriction X).obj F)
          ((restriction X).obj G.obj) ((restriction X).obj H.obj)) :=
  rfl

end QCoh

end AlgebraicGeometry.GroupoidsOver
