module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FreeFlatCover.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Definition
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Existence obstructions for extensions on a first-order thickening

A prescribed infinitesimal map determines an Ext² class by a flat cover,
an injective embedding, and descent of the resulting quotient extension.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} (π : 𝒪' ⟶ 𝒪)
variable [hπ : IsFirstOrderThickening π]
variable [HasFunctorialInjectives (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]
variable [(SheafOfModules.restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J 𝒪')]

-- Concrete public data may depend on private proof certificates. This compiler
-- compatibility option keeps those certificates out of the reusable API.
set_option backward.privateInPublic true

namespace ExistenceObstructionConstruction

/-- The kernel sequence of the canonical free flat cover of a restricted module. -/
private def flatCoverKernelSequence
    (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :=
  ShortComplex.kernelSequence (FreeFlatCover.πApp ((restrictionAlong π).obj F))

/-- The kernel sequence of the canonical free flat cover is short exact. -/
private theorem flatCoverKernelSequence_shortExact
    (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    (flatCoverKernelSequence π F).ShortExact := sorry

/-- The kernel-ideal action on the free flat cover is killed by its covering map. -/
private theorem action_flatCover_comp_πApp
    (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    IdealSheaf.action (KernelIdeal.subobject π)
          (FreeFlatCover.obj ((restrictionAlong π).obj F)) ≫
        FreeFlatCover.πApp ((restrictionAlong π).obj F) = 0 := sorry

/-- The kernel-ideal action on the cover lifted to the kernel of its projection. -/
private def liftedIdealAction
    (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :=
  kernel.lift (FreeFlatCover.πApp ((restrictionAlong π).obj F))
    (IdealSheaf.action (KernelIdeal.subobject π)
      (FreeFlatCover.obj ((restrictionAlong π).obj F)))
    (action_flatCover_comp_πApp π F)

/-- The lifted ideal action descends through the tensor of the kernel inclusion. -/
private theorem idealQuotientIncl_zero
    (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    (tensorLeft (KernelIdeal.sheaf π)).map
        (kernel.ι (FreeFlatCover.πApp ((restrictionAlong π).obj F))) ≫
      (liftedIdealAction π F ≫
        cokernel.π (IdealSheaf.action (KernelIdeal.subobject π)
          (kernel (FreeFlatCover.πApp ((restrictionAlong π).obj F))))) = 0 := sorry

/-- The comparison from the ideal tensor quotient to the kernel modulo ideal action. -/
private def idealQuotientIncl
    (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :=
  cokernel.desc
    ((tensorLeft (KernelIdeal.sheaf π)).map
      (kernel.ι (FreeFlatCover.πApp ((restrictionAlong π).obj F))))
    (liftedIdealAction π F ≫
      cokernel.π (IdealSheaf.action (KernelIdeal.subobject π)
        (kernel (FreeFlatCover.πApp ((restrictionAlong π).obj F)))))
    (idealQuotientIncl_zero π F)

include hπ in
/-- The ideal quotient comparison is monomorphic after extension of scalars. -/
private theorem idealQuotientIncl_extendScalars_mono
    (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    Mono ((ChangeOfRings.extendScalars (ringSheafMap π)).map
      (idealQuotientIncl π F)) := sorry

/-- The prescribed infinitesimal map expressed over the source ring sheaf. -/
private def restrictedComparison
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    moduleTensor (KernelIdeal.sheaf π) ((restrictionAlong π).obj F) ⟶
      (restrictionAlong π).obj K :=
  moduleTensorMap (restrictIdealModuleIso hπ.isSquareZero).inv (𝟙 _) ≫
    Restriction.tensorComparison π (ideal π) F ≫ (restrictionAlong π).map c

/-- Tensoring the cover projection and applying the prescribed map kills the kernel tensor. -/
private theorem idealQuotientToKernel_comp_zero
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    (tensorLeft (KernelIdeal.sheaf π)).map
        (kernel.ι (FreeFlatCover.πApp ((restrictionAlong π).obj F))) ≫
      ((tensorLeft (KernelIdeal.sheaf π)).map
          (FreeFlatCover.πApp ((restrictionAlong π).obj F)) ≫
        restrictedComparison π F K c) = 0 := sorry

/-- The map from the ideal tensor quotient to the prescribed coefficient module. -/
private def idealQuotientToKernel
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :=
  cokernel.desc
    ((tensorLeft (KernelIdeal.sheaf π)).map
      (kernel.ι (FreeFlatCover.πApp ((restrictionAlong π).obj F))))
    ((tensorLeft (KernelIdeal.sheaf π)).map
        (FreeFlatCover.πApp ((restrictionAlong π).obj F)) ≫
      restrictedComparison π F K c)
    (idealQuotientToKernel_comp_zero π F K c)

/-- The extension of the ideal quotient map into an injective coefficient module. -/
private def liftThroughInjective
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) [Injective K]
    (c : moduleTensor (ideal π) F ⟶ K) :=
  -- The canonical factorization API requires its monomorphism certificate explicitly.
  @Injective.factorThru (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) _
    K _ _ ‹Injective K›
    ((ChangeOfRings.extendScalars (ringSheafMap π)).map (idealQuotientToKernel π F K c) ≫
      (ChangeOfRings.extendRestrictAdjunction (ringSheafMap π)).counit.app K)
    ((ChangeOfRings.extendScalars (ringSheafMap π)).map (idealQuotientIncl π F))
    (idealQuotientIncl_extendScalars_mono π F)

/-- The map from the flat-cover kernel into an injective coefficient module. -/
private def injectiveKernelMap
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) [Injective K]
    (c : moduleTensor (ideal π) F ⟶ K) :=
  cokernel.π (IdealSheaf.action (KernelIdeal.subobject π)
      (kernel (FreeFlatCover.πApp ((restrictionAlong π).obj F)))) ≫
    (ChangeOfRings.extendRestrictAdjunction (ringSheafMap π)).unit.app _ ≫
    (restrictionAlong π).map (liftThroughInjective π F K c)

/-- The inclusion into the pushout with injective coefficients. -/
private def injectiveEnvelopeIncl
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) [Injective K]
    (c : moduleTensor (ideal π) F ⟶ K) :=
  pushout.inl (injectiveKernelMap π F K c)
    (kernel.ι (FreeFlatCover.πApp ((restrictionAlong π).obj F)))

/-- The quotient projection from the pushout with injective coefficients. -/
private def injectiveEnvelopeProj
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) [Injective K]
    (c : moduleTensor (ideal π) F ⟶ K) :
    pushout (injectiveKernelMap π F K c)
        (kernel.ι (FreeFlatCover.πApp ((restrictionAlong π).obj F))) ⟶
      (restrictionAlong π).obj F :=
  pushout.desc 0 (FreeFlatCover.πApp ((restrictionAlong π).obj F)) (by simp)

/-- The inclusion and projection of the injective pushout compose to zero. -/
private theorem injectiveEnvelopeSequence_zero
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) [Injective K]
    (c : moduleTensor (ideal π) F ⟶ K) :
    injectiveEnvelopeIncl π F K c ≫ injectiveEnvelopeProj π F K c = 0 := sorry

/-- The pushout of the flat-cover kernel sequence with injective coefficients. -/
private def injectiveEnvelopeSequence
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) [Injective K]
    (c : moduleTensor (ideal π) F ⟶ K) :=
  ShortComplex.mk (injectiveEnvelopeIncl π F K c) (injectiveEnvelopeProj π F K c)
    (injectiveEnvelopeSequence_zero π F K c)

/-- The injective pushout sequence is short exact. -/
private theorem injectiveEnvelopeSequence_shortExact
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) [Injective K]
    (c : moduleTensor (ideal π) F ⟶ K) :
    (injectiveEnvelopeSequence π F K c).ShortExact := sorry

/-- The infinitesimal map of the injective pushout is the prescribed map. -/
private theorem injectiveEnvelopeSequence_infMap
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) [Injective K]
    (c : moduleTensor (ideal π) F ⟶ K) :
    infMap hπ.isSquareZero
      (ofMaps π K (injectiveEnvelopeSequence π F K c).X₂ F
        (injectiveEnvelopeSequence π F K c).f (injectiveEnvelopeSequence π F K c).g
        (injectiveEnvelopeSequence π F K c).zero
        (injectiveEnvelopeSequence_shortExact π F K c)) = c := sorry

/-- The cokernel sequence of the chosen injective embedding. -/
private def injectiveCokernelSequence
    (K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :=
  ShortComplex.cokernelSequence (HasFunctorialInjectives.ι.app K)

/-- The cokernel sequence of the chosen injective embedding is short exact. -/
private theorem injectiveCokernelSequence_shortExact
    (K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    (injectiveCokernelSequence K).ShortExact := sorry

/-- The inclusion of the injective cokernel into the quotient pushout. -/
private def envelopePushoutIncl
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :=
  pushout.inl ((restrictionAlong π).map (cokernel.π (HasFunctorialInjectives.ι.app K)))
    (injectiveEnvelopeSequence π F (HasFunctorialInjectives.obj K)
      (c ≫ HasFunctorialInjectives.ι.app K)).f

/-- The quotient projection from the pushout by the injective-cokernel map. -/
private def envelopePushoutProj
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    pushout ((restrictionAlong π).map (cokernel.π (HasFunctorialInjectives.ι.app K)))
        (injectiveEnvelopeSequence π F (HasFunctorialInjectives.obj K)
          (c ≫ HasFunctorialInjectives.ι.app K)).f ⟶ (restrictionAlong π).obj F :=
  pushout.desc 0
    (injectiveEnvelopeSequence π F (HasFunctorialInjectives.obj K)
      (c ≫ HasFunctorialInjectives.ι.app K)).g
    (by
      rw [comp_zero]
      exact (injectiveEnvelopeSequence π F (HasFunctorialInjectives.obj K)
        (c ≫ HasFunctorialInjectives.ι.app K)).zero.symm)

/-- The inclusion and projection of the quotient pushout compose to zero. -/
private theorem envelopePushoutSequence_zero
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    envelopePushoutIncl π F K c ≫ envelopePushoutProj π F K c = 0 := sorry

/-- The injective envelope pushed out along its coefficient cokernel. -/
private def envelopePushoutSequence
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :=
  ShortComplex.mk (envelopePushoutIncl π F K c) (envelopePushoutProj π F K c)
    (envelopePushoutSequence_zero π F K c)

/-- The quotient pushout sequence is short exact. -/
private theorem envelopePushoutSequence_shortExact
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    (envelopePushoutSequence π F K c).ShortExact := sorry

/-- The infinitesimal map of the quotient pushout vanishes. -/
private theorem envelopePushoutSequence_infMap_eq_zero
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    infMap hπ.isSquareZero
      (ofMaps π (cokernel (HasFunctorialInjectives.ι.app K))
        (envelopePushoutSequence π F K c).X₂ F
        (envelopePushoutSequence π F K c).f (envelopePushoutSequence π F K c).g
        (envelopePushoutSequence π F K c).zero
        (envelopePushoutSequence_shortExact π F K c)) = 0 := sorry

/-- The inclusion into the descended quotient module. -/
private def descendedIncl
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :=
  (restrictHomEquivOfIsLocallySurjective (ringSheafMap π)
      (cokernel (HasFunctorialInjectives.ι.app K))
      ((ChangeOfRings.extendScalars (ringSheafMap π)).obj
        (envelopePushoutSequence π F K c).X₂)).symm
    ((envelopePushoutSequence π F K c).f ≫
      (ChangeOfRings.extendRestrictAdjunction (ringSheafMap π)).unit.app _)

/-- The projection from the descended quotient module. -/
private def descendedProj
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :=
  (ChangeOfRings.extendScalars (ringSheafMap π)).map
      (envelopePushoutSequence π F K c).g ≫
    (ChangeOfRings.extendRestrictAdjunction (ringSheafMap π)).counit.app F

/-- The inclusion and projection of the descended sequence compose to zero. -/
private theorem descendedSequence_zero
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    descendedIncl π F K c ≫ descendedProj π F K c = 0 := sorry

/-- The scalar-descended quotient sequence over the target ring sheaf. -/
private def descendedSequence
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :=
  ShortComplex.mk (descendedIncl π F K c) (descendedProj π F K c)
    (descendedSequence_zero π F K c)

/-- The descended quotient sequence is short exact. -/
private theorem descendedSequence_shortExact
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    (descendedSequence π F K c).ShortExact := sorry

end ExistenceObstructionConstruction

variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]

/-- The Ext² obstruction obtained by composing the descended quotient extension
with the chosen injective-cokernel extension. -/
def existenceObstruction
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) : Ext F K 2 :=
  (ExistenceObstructionConstruction.descendedSequence_shortExact π F K c).extClass.comp
    (ExistenceObstructionConstruction.injectiveCokernelSequence_shortExact K).extClass (rfl : 1 + 1 = 2)

/-- The existence obstruction vanishes exactly when a short exact sequence with
the prescribed infinitesimal map exists over the source ring sheaf. -/
theorem existenceObstruction_eq_zero_iff
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    existenceObstruction π F K c = 0 ↔
      ∃ (M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')
        (a : (restrictionAlong π).obj K ⟶ M)
        (b : M ⟶ (restrictionAlong π).obj F) (hab : a ≫ b = 0)
        (hS : (ShortComplex.mk a b hab).ShortExact),
        infMap hπ.isSquareZero (ofMaps π K M F a b hab hS) = c := sorry

end SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension
