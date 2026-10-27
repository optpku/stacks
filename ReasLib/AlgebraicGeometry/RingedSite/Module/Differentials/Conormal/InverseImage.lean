/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse image of conormal modules

This file constructs the conormal comparison attached to a commutative square of ring-sheaf
morphisms on two sites.  The input is the adjoint-side square, so the construction applies to an
arbitrary presentation rather than only to a chosen polynomial presentation.  The base arrow of a
composable presentation is deliberately absent: its conormal term depends only on the second
arrow.

The sectionwise map on `I / I ^ 2` is explicit.  Sheafification, extension of scalars, and the
pullback-pushforward adjunction then produce the sheaf comparison.  Representable flatness is used
only for invertibility, together with invertibility of the two transposed vertical maps.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite.InverseImage

noncomputable section

universe u

namespace SheafOfModules
namespace RingedSite
namespace Conormal
namespace InverseImage
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [F.IsContinuous J K]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify K CommRingCat.{u}]
variable [HasWeakSheafify K AddCommGrpCat.{u}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ Q : Cᵒᵖ ⥤ CommRingCat.{u}, F.op.HasLeftKanExtension Q]

variable {P B : Sheaf J CommRingCat.{u}}
variable {P' B' : Sheaf K CommRingCat.{u}}
variable {alpha : P ⟶ B} {alpha' : P' ⟶ B'}

/-- A commutative adjoint-side square sends the kernel ideal of `alpha` into the kernel ideal of
`alpha'` on every object of the source site. -/
theorem ideal_le_comap
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    (U : Cᵒᵖ) :
    conormalIdeal alpha U ≤
      (conormalIdeal alpha' (F.op.obj U)).comap ((middle.hom.app U).hom) := sorry

/-- The sectionwise map on cotangent modules induced by an adjoint-side commutative square. -/
noncomputable abbrev cotangentApp
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    (U : Cᵒᵖ) :
    conormalObj alpha U ⟶
      (ModuleCat.restrictScalars ((middle.hom.app U).hom)).obj
        (conormalObj alpha' (F.op.obj U)) :=
  ConcreteCategory.ofHom (C := ModuleCat (P.obj.obj U))
    (@Ideal.mapCotangent
      (P.obj.obj U) _ (P.obj.obj U) (P'.obj.obj (F.op.obj U)) _ _
      (Algebra.id (P.obj.obj U)) ((middle.hom.app U).hom.toAlgebra)
      (conormalIdeal alpha U) (conormalIdeal alpha' (F.op.obj U))
      (@Algebra.ofId (P.obj.obj U) (P'.obj.obj (F.op.obj U)) _ _
        ((middle.hom.app U).hom.toAlgebra))
      (ideal_le_comap F middle target square U))

/-- On a cotangent generator, `cotangentApp` applies the middle vertical map to its kernel
representative. -/
theorem cotangentApp_toCotangent
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    (U : Cᵒᵖ) (x : conormalIdeal alpha U) :
    cotangentApp F middle target square U ((conormalIdeal alpha U).toCotangent x) =
      (conormalIdeal alpha' (F.op.obj U)).toCotangent
        ⟨(middle.hom.app U).hom x, ideal_le_comap F middle target square U x.2⟩ := sorry

/-- The target conormal sheaf, pushed to the source site along the target vertical map. -/
@[stacks 08TM "pushed conormal source"]
abbrev pushedSource
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (alpha' : P' ⟶ B') :
    ringedSiteModuleCategory J B :=
  (SheafOfModules.pushforward (underlyingMap F target)).obj (conormalSource alpha')

/-- The section function from the source conormal presheaf to the pushed target conormal sheaf. -/
noncomputable def comparisonApply
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    (U : Cᵒᵖ) (x : conormalObj alpha U) :
    ((restrictionAlong alpha).obj (pushedSource F target alpha')).val.obj U :=
  ((conormalSourcePresheafUnit alpha').app (F.op.obj U))
    (cotangentApp F middle target square U x)

/-- The sectionwise conormal comparison is additive. -/
theorem comparisonApply_add
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    (U : Cᵒᵖ) (x y : conormalObj alpha U) :
    comparisonApply F middle target square U (x + y) =
      comparisonApply F middle target square U x +
        comparisonApply F middle target square U y := sorry

/-- The sectionwise conormal comparison is linear over the source presenting ring. -/
theorem comparisonApply_smul
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    (U : Cᵒᵖ) (r : P.obj.obj U) (x : conormalObj alpha U) :
    comparisonApply F middle target square U (r • x) =
      r • comparisonApply F middle target square U x := sorry

/-- The sectionwise conormal comparison as a morphism of module categories. -/
@[stacks 08TM "sectionwise conormal inverse-image comparison"]
noncomputable def comparisonApp
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    (U : Cᵒᵖ) :
    conormalObj alpha U ⟶
      ((restrictionAlong alpha).obj (pushedSource F target alpha')).val.obj U :=
  ConcreteCategory.ofHom (C := ModuleCat (P.obj.obj U))
    { toFun := comparisonApply F middle target square U
      map_add' := comparisonApply_add F middle target square U
      map_smul' := comparisonApply_smul F middle target square U }

/-- On a cotangent generator, the sectionwise comparison is the target sheafification unit
applied after the middle vertical map. -/
theorem comparisonApp_toCotangent
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    (U : Cᵒᵖ) (x : conormalIdeal alpha U) :
    comparisonApp F middle target square U ((conormalIdeal alpha U).toCotangent x) =
      ((conormalSourcePresheafUnit alpha').app (F.op.obj U))
        ((conormalIdeal alpha' (F.op.obj U)).toCotangent
          ⟨(middle.hom.app U).hom x,
            ideal_le_comap F middle target square U x.2⟩) := sorry

/-- The sectionwise conormal comparisons commute with restriction on the source site. -/
theorem comparisonApp_naturality
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (conormalPresheaf alpha).map i ≫
        (ModuleCat.restrictScalars (((ringSheaf J P).obj.map i).hom)).map
          (comparisonApp F middle target square V) =
      comparisonApp F middle target square U ≫
        (((restrictionAlong alpha).obj (pushedSource F target alpha')).val.map i) := sorry

/-- The presheaf morphism underlying the conormal inverse-image comparison. -/
@[stacks 08TM "conormal inverse-image presheaf comparison"]
noncomputable def comparisonPresheaf
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target) :
    conormalPresheaf alpha ⟶
      ((restrictionAlong alpha).obj (pushedSource F target alpha')).val where
  app U := comparisonApp F middle target square U
  naturality i := comparisonApp_naturality F middle target square i

/-- The conormal comparison after sheafification, still viewed over the source presenting ring. -/
@[stacks 08TM "conormal inverse-image comparison before scalar extension"]
noncomputable def comparisonOverMiddle
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target) :
    conormalSourceOverSource alpha ⟶
      (restrictionAlong alpha).obj (pushedSource F target alpha') :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringSheaf J P).obj)).homEquiv _ _).symm
    (comparisonPresheaf F middle target square)

/-- The adjoint-side comparison between the scalar-extended conormal terms. -/
@[stacks 08TM "adjoint conormal inverse-image comparison"]
noncomputable def comparisonAdjoint
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target) :
    conormalSource alpha ⟶ pushedSource F target alpha' :=
  ((extendRestrictAdj alpha).homEquiv _ _).symm
    (comparisonOverMiddle F middle target square)

/-- The inverse-image comparison on conormal terms induced by an adjoint-side commutative square.
For a full composable presentation, this construction depends only on its second square. -/
@[stacks 08TM "conormal inverse-image comparison"]
noncomputable def comparison
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    [(SheafOfModules.pushforward (underlyingMap F target)).IsRightAdjoint] :
    (SheafOfModules.pullback (underlyingMap F target)).obj (conormalSource alpha) ⟶
      conormalSource alpha' :=
  ((SheafOfModules.pullbackPushforwardAdjunction
    (underlyingMap F target)).homEquiv _ _).symm
      (comparisonAdjoint F middle target square)

/-- Transposing `comparison` recovers its explicit adjoint-side morphism. -/
@[simp]
theorem comparison_adj
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    [(SheafOfModules.pushforward (underlyingMap F target)).IsRightAdjoint] :
    (SheafOfModules.pullbackPushforwardAdjunction
      (underlyingMap F target)).homEquiv _ _
        (comparison F middle target square) =
      comparisonAdjoint F middle target square := by
  exact Equiv.apply_symm_apply _ _

private def kernelToConormal (alpha : P ⟶ B) :
    KernelIdeal.sheaf alpha ⟶ (restrictionAlong alpha).obj (conormalSource alpha) where
  val :=
    { app U := ConcreteCategory.ofHom
        (((conormalSourcePresheafUnit alpha).app U).hom.comp
          ((conormalIdeal alpha U).toCotangent.comp
            (KernelIdeal.sectionsIso alpha U).hom.hom))
      naturality := by
        intro U V i
        ext x
        have hx :
            (KernelIdeal.sectionsIso alpha V).hom
                ((KernelIdeal.sheaf alpha).val.map i x) =
              ⟨(P.obj.map i).hom ((KernelIdeal.sectionsIso alpha U).hom x),
                conormalIdeal_le_comap alpha i ((KernelIdeal.sectionsIso alpha U).hom x).2⟩ := by
          apply Subtype.ext
          change ((KernelIdeal.sectionsIso alpha V).hom
            ((KernelIdeal.sheaf alpha).val.map i x) : P.obj.obj V) =
              (P.obj.map i).hom ((KernelIdeal.sectionsIso alpha U).hom x)
          rw [KernelIdeal.sectionsIso_hom_coe, KernelIdeal.sectionsIso_hom_coe]
          exact ConcreteCategory.congr_hom ((KernelIdeal.ι alpha).val.naturality i) x
        change (conormalSourcePresheafUnit alpha).app V
            ((conormalIdeal alpha V).toCotangent
              ((KernelIdeal.sectionsIso alpha V).hom
                ((KernelIdeal.sheaf alpha).val.map i x))) = _
        rw [hx, ← conormalRestriction_toCotangent alpha i]
        exact ConcreteCategory.congr_hom
          ((conormalSourcePresheafUnit alpha).naturality i) _ }

private theorem adjoint_square
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target) :
    (ringPullback (J := J) (K := K) F).map alpha ≫ adjointMap F target =
      adjointMap F middle ≫ alpha' :=
  (F.sheafAdjunctionContinuous CommRingCat.{u} J K).homEquiv_naturality_right_square
    alpha target middle alpha' square.w.symm

private instance additiveForgetPreservesSheafification :
    K.PreservesSheafification
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}) where
  le := by
    intro P Q f hf
    have h := (K.W_iff_isLocallyBijective f).mp hf
    apply (K.W_iff_isLocallyBijective
      (Functor.whiskerRight f (forget₂ CommRingCat.{u} RingCat.{u} ⋙
        forget₂ RingCat.{u} AddCommGrpCat.{u}))).mpr
    constructor
    · exact ⟨fun x y hxy ↦ h.1.equalizerSieve_mem x y hxy⟩
    · exact ⟨fun x ↦ h.2.imageSieve_mem x⟩

private def additiveCoefficientIso [RepresentablyFlat F]
    (O : Sheaf J CommRingCat.{u}) :
    (F.sheafPullback AddCommGrpCat.{u} J K).obj
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})).obj O) ≅
      (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})).obj
        ((ringPullback (J := J) (K := K) F).obj O) :=
  ((Functor.sheafPullback.compSheafComposeIso F
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}) J K).app O).symm

private instance additivePullbackExact [RepresentablyFlat F] :
    CategoryTheory.Limits.PreservesFiniteLimits
      (F.sheafPullback AddCommGrpCat.{u} J K) := by
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

private def additiveVerticalIso [RepresentablyFlat F]
    {O : Sheaf J CommRingCat.{u}} {O' : Sheaf K CommRingCat.{u}}
    (m : O ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj O')
    [IsIso (adjointMap (J := J) (K := K) F m)] :
    (F.sheafPullback AddCommGrpCat.{u} J K).obj
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u} ⋙
          forget₂ RingCat.{u} AddCommGrpCat.{u})).obj O) ≅
      (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u} ⋙
        forget₂ RingCat.{u} AddCommGrpCat.{u})).obj O' :=
  additiveCoefficientIso F O ≪≫
    (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u} ⋙
      forget₂ RingCat.{u} AddCommGrpCat.{u})).mapIso (asIso (adjointMap F m))

set_option backward.isDefEq.respectTransparency false in
private theorem additive_square [RepresentablyFlat F]
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    [IsIso (adjointMap (J := J) (K := K) F middle)]
    [IsIso (adjointMap (J := J) (K := K) F target)] :
    (F.sheafPullback AddCommGrpCat.{u} J K).map
        ((SheafOfModules.toSheaf (ringSheaf J P)).map (KernelIdeal.map alpha)) ≫
        (additiveVerticalIso F target).hom =
      (additiveVerticalIso F middle).hom ≫
        (SheafOfModules.toSheaf (ringSheaf K P')).map (KernelIdeal.map alpha') := by
  have hn := (Functor.sheafPullback.compSheafComposeIso F
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
    J K).inv.naturality alpha
  change (F.sheafPullback AddCommGrpCat.{u} J K).map
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u} ⋙
        forget₂ RingCat.{u} AddCommGrpCat.{u})).map alpha) ≫
      (additiveCoefficientIso F B).hom =
    (additiveCoefficientIso F P).hom ≫
      (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u} ⋙
        forget₂ RingCat.{u} AddCommGrpCat.{u})).map
        ((ringPullback (J := J) (K := K) F).map alpha) at hn
  have hs := congrArg
    ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u} ⋙
      forget₂ RingCat.{u} AddCommGrpCat.{u})).map)
    (adjoint_square F middle target square)
  change (F.sheafPullback AddCommGrpCat.{u} J K).map
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u} ⋙
        forget₂ RingCat.{u} AddCommGrpCat.{u})).map alpha) ≫
      ((additiveCoefficientIso F B).hom ≫ _) =
    ((additiveCoefficientIso F P).hom ≫ _) ≫
      (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u} ⋙
        forget₂ RingCat.{u} AddCommGrpCat.{u})).map alpha'
  change _ ≫ ((additiveCoefficientIso F B).hom ≫ _) = _
  rw [← Category.assoc, hn, Category.assoc]
  simpa only [Functor.map_comp, Category.assoc, Functor.mapIso_hom, asIso_hom] using
    congrArg (fun t ↦ (additiveCoefficientIso F P).hom ≫ t) hs

set_option backward.isDefEq.respectTransparency false in
private def additiveKernelIso [RepresentablyFlat F]
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    [IsIso (adjointMap (J := J) (K := K) F middle)]
    [IsIso (adjointMap (J := J) (K := K) F target)] :
    (F.sheafPullback AddCommGrpCat.{u} J K).obj
        ((SheafOfModules.toSheaf (ringSheaf J P)).obj (KernelIdeal.sheaf alpha)) ≅
      (SheafOfModules.toSheaf (ringSheaf K P')).obj (KernelIdeal.sheaf alpha') :=
  (F.sheafPullback AddCommGrpCat.{u} J K).mapIso (KernelIdeal.underlyingKernelIso alpha) ≪≫
    CategoryTheory.Limits.PreservesKernel.iso (F.sheafPullback AddCommGrpCat.{u} J K)
      ((SheafOfModules.toSheaf (ringSheaf J P)).map (KernelIdeal.map alpha)) ≪≫
    CategoryTheory.Limits.kernel.mapIso
      ((F.sheafPullback AddCommGrpCat.{u} J K).map
        ((SheafOfModules.toSheaf (ringSheaf J P)).map (KernelIdeal.map alpha)))
      ((SheafOfModules.toSheaf (ringSheaf K P')).map (KernelIdeal.map alpha'))
      (additiveVerticalIso F middle) (additiveVerticalIso F target)
      (additive_square F middle target square) ≪≫
    (KernelIdeal.underlyingKernelIso alpha').symm

section Reverse

variable [RepresentablyFlat F]
variable (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
variable (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
variable (square : CommSq middle alpha
  ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
variable [(SheafOfModules.pushforward (underlyingMap F target)).IsRightAdjoint]
variable [IsIso (adjointMap (J := J) (K := K) F middle)]
variable [IsIso (adjointMap (J := J) (K := K) F target)]

private abbrev inverseTarget : ringedSiteModuleCategory K B' :=
  (SheafOfModules.pullback (underlyingMap F target)).obj (conormalSource alpha)

private def kernelToPushed :
    (SheafOfModules.toSheaf (ringSheaf J P)).obj (KernelIdeal.sheaf alpha) ⟶
      (F.sheafPushforwardContinuous AddCommGrpCat.{u} J K).obj
        ((SheafOfModules.toSheaf (ringSheaf K B')).obj
          (inverseTarget (alpha := alpha) F target)) :=
  (SheafOfModules.toSheaf (ringSheaf J P)).map (kernelToConormal alpha) ≫
    (SheafOfModules.toSheaf (ringSheaf J B)).map
      ((SheafOfModules.pullbackPushforwardAdjunction (underlyingMap F target)).unit.app
        (conormalSource alpha))

private def inverseKernelAdd :
    (SheafOfModules.toSheaf (ringSheaf K P')).obj (KernelIdeal.sheaf alpha') ⟶
      (SheafOfModules.toSheaf (ringSheaf K B')).obj
        (inverseTarget (alpha := alpha) F target) :=
  (additiveKernelIso F middle target square).inv ≫
    ((F.sheafAdjunctionContinuous AddCommGrpCat.{u} J K).homEquiv _ _).symm
      (kernelToPushed (alpha := alpha) F target)

private def inverseKernelSection (U : Dᵒᵖ) (x : conormalIdeal alpha' U) :
    ((restrictionAlong alpha').obj
      (inverseTarget (alpha := alpha) F target)).val.obj U :=
  (inverseKernelAdd F middle target square).hom.app U
    ((KernelIdeal.sectionsIso alpha' U).inv x)

/-- The inverse-image transport of kernel sections is linear, annihilates products in the
kernel, and commutes with restriction. -/
private theorem comparisonInv_laws :
    (∀ (U : Dᵒᵖ) (r : P'.obj.obj U) (x : conormalIdeal alpha' U),
      inverseKernelSection F middle target square U (r • x) =
        r • inverseKernelSection F middle target square U x) ∧
    (∀ (U : Dᵒᵖ) (x y : conormalIdeal alpha' U),
      inverseKernelSection F middle target square U (x * y) = 0) ∧
    (∀ {U V : Dᵒᵖ} (i : U ⟶ V) (x : conormalIdeal alpha' U),
      inverseKernelSection F middle target square V
          ⟨(P'.obj.map i).hom x, conormalIdeal_le_comap alpha' i x.2⟩ =
        ((inverseTarget (alpha := alpha) F target).val.map i)
          (inverseKernelSection F middle target square U x)) := sorry

private def inverseKernelLinear (U : Dᵒᵖ) :
    conormalIdeal alpha' U →ₗ[P'.obj.obj U]
      ((restrictionAlong alpha').obj
        (inverseTarget (alpha := alpha) F target)).val.obj U where
  toFun := inverseKernelSection F middle target square U
  map_add' x y := by
    change ((inverseKernelAdd F middle target square).hom.app U).hom
        ((KernelIdeal.sectionsIso alpha' U).inv (x + y)) = _
    rw [map_add]
    exact ((inverseKernelAdd F middle target square).hom.app U).hom.map_add _ _
  map_smul' := (comparisonInv_laws F middle target square).1 U

private def inverseCotangentApp (U : Dᵒᵖ) :
    conormalObj alpha' U ⟶
      ((restrictionAlong alpha').obj
        (inverseTarget (alpha := alpha) F target)).val.obj U :=
  ConcreteCategory.ofHom
    (Ideal.Cotangent.lift (inverseKernelLinear F middle target square U)
      ((comparisonInv_laws F middle target square).2.1 U))

private def inverseCotangentPresheaf :
    conormalPresheaf alpha' ⟶
      ((restrictionAlong alpha').obj
        (inverseTarget (alpha := alpha) F target)).val where
  app := inverseCotangentApp F middle target square
  naturality := by
    intro U V i
    ext x
    obtain ⟨x, rfl⟩ := (conormalIdeal alpha' U).toCotangent_surjective x
    change inverseCotangentApp F middle target square V
        (conormalRestriction alpha' i ((conormalIdeal alpha' U).toCotangent x)) = _
    rw [conormalRestriction_toCotangent]
    exact (comparisonInv_laws F middle target square).2.2 i x

/-- The reverse conormal comparison descends the transported kernel sections through their
square quotient and extends scalars to the target ring sheaf. -/
@[stacks 08TM "conormal inverse-image comparison inverse", no_expose]
noncomputable def comparisonInv :
    conormalSource alpha' ⟶
      (SheafOfModules.pullback (underlyingMap F target)).obj (conormalSource alpha) :=
  ((extendRestrictAdj alpha').homEquiv _ _).symm
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf K P').obj)).homEquiv _ _).symm
      (inverseCotangentPresheaf F middle target square))

end Reverse

/-- The conormal comparison followed by its named inverse is the identity. -/
@[simp, stacks 08TM "conormal comparison inverse law"]
theorem comparison_hom_inv_id
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    [(SheafOfModules.pushforward (underlyingMap F target)).IsRightAdjoint]
    [RepresentablyFlat F] [IsIso (adjointMap F middle)] [IsIso (adjointMap F target)] :
    comparison F middle target square ≫ comparisonInv F middle target square = 𝟙 _ := sorry

/-- The named inverse followed by the conormal comparison is the identity. -/
@[simp, stacks 08TM "conormal inverse comparison law"]
theorem comparison_inv_hom_id
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    [(SheafOfModules.pushforward (underlyingMap F target)).IsRightAdjoint]
    [RepresentablyFlat F] [IsIso (adjointMap F middle)] [IsIso (adjointMap F target)] :
    comparisonInv F middle target square ≫ comparison F middle target square = 𝟙 _ := sorry

/-- The conormal inverse-image comparison assembled from its named maps and inverse laws. -/
@[stacks 08TM "conormal inverse-image comparison isomorphism"]
noncomputable def comparisonIso
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    [(SheafOfModules.pushforward (underlyingMap F target)).IsRightAdjoint]
    [RepresentablyFlat F] [IsIso (adjointMap F middle)] [IsIso (adjointMap F target)] :
    (SheafOfModules.pullback (underlyingMap F target)).obj (conormalSource alpha) ≅
      conormalSource alpha' where
  hom := comparison F middle target square
  inv := comparisonInv F middle target square
  hom_inv_id := comparison_hom_inv_id F middle target square
  inv_hom_id := comparison_inv_hom_id F middle target square

/-- A representably flat inverse image preserves the conormal module when its two
vertical ring maps are inverse-image isomorphisms. -/
@[stacks 08TM "conormal inverse-image comparison is an isomorphism"]
instance comparison_isIso
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    [(SheafOfModules.pushforward (underlyingMap F target)).IsRightAdjoint]
    [RepresentablyFlat F] [IsIso (adjointMap F middle)] [IsIso (adjointMap F target)] :
    IsIso (comparison F middle target square) :=
  (comparisonIso F middle target square).isIso_hom

/-- The forward map of `comparisonIso` is the canonical conormal inverse-image comparison. -/
@[stacks 08TM "conormal inverse-image comparison isomorphism hom", simp]
theorem comparisonIso_hom
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    [(SheafOfModules.pushforward (underlyingMap F target)).IsRightAdjoint]
    [RepresentablyFlat F] [IsIso (adjointMap F middle)] [IsIso (adjointMap F target)] :
    (comparisonIso F middle target square).hom =
      comparison F middle target square := rfl

/-- The inverse map of `comparisonIso` is the named conormal comparison inverse. -/
@[stacks 08TM "conormal inverse-image comparison isomorphism inverse", simp]
theorem comparisonIso_inv
    (middle : P ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj P')
    (target : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj B')
    (square : CommSq middle alpha
      ((F.sheafPushforwardContinuous CommRingCat.{u} J K).map alpha') target)
    [(SheafOfModules.pushforward (underlyingMap F target)).IsRightAdjoint]
    [RepresentablyFlat F] [IsIso (adjointMap F middle)] [IsIso (adjointMap F target)] :
    (comparisonIso F middle target square).inv =
      comparisonInv F middle target square := rfl

section Canonical

variable {O₂ O₃ : Sheaf J CommRingCat.{u}}

/-- The inverse-image morphism obtained by applying ring-sheaf pullback. -/
@[stacks 08TM "inverse-image ring-sheaf morphism"]
abbrev pullbackMap (alpha : O₂ ⟶ O₃) :
    (ringPullback
        (J := J) (K := K) F).obj O₂ ⟶
      (ringPullback
        (J := J) (K := K) F).obj O₃ :=
  (ringPullback
    (J := J) (K := K) F).map alpha

/-- The canonical conormal comparison for an arbitrary ring-sheaf morphism and its inverse
image. -/
@[stacks 08TM "canonical conormal inverse-image comparison"]
noncomputable abbrev pullbackComparison
    (alpha : O₂ ⟶ O₃)
    [(SheafOfModules.pushforward
      (structureMap
        (J := J) (K := K) F O₃)).IsRightAdjoint] :
    (modulePullback
      (J := J) (K := K) F O₃).obj (conormalSource alpha) ⟶
      conormalSource (pullbackMap F alpha) :=
  comparison (J := J) (K := K) F
    (ringUnit (J := J) (K := K) F O₂)
    (ringUnit (J := J) (K := K) F O₃)
    (ringUnitSquare (J := J) (K := K) F alpha)

/-- The named inverse of the canonical conormal inverse-image comparison. -/
@[stacks 08TM "canonical conormal inverse-image comparison inverse"]
noncomputable def pullbackComparisonInv
    [RepresentablyFlat F] (alpha : O₂ ⟶ O₃)
    [(SheafOfModules.pushforward
      (structureMap
        (J := J) (K := K) F O₃)).IsRightAdjoint] :
    conormalSource (pullbackMap F alpha) ⟶
      (modulePullback
        (J := J) (K := K) F O₃).obj (conormalSource alpha) :=
  comparisonInv (J := J) (K := K) F
    (ringUnit (J := J) (K := K) F O₂)
    (ringUnit (J := J) (K := K) F O₃)
    (ringUnitSquare (J := J) (K := K) F alpha)

/-- The canonical pullback comparison followed by its named inverse is the identity. -/
@[simp, stacks 08TM "canonical conormal comparison inverse law"]
theorem pullbackComparison_hom_inv_id
    [RepresentablyFlat F] (alpha : O₂ ⟶ O₃)
    [(SheafOfModules.pushforward
      (structureMap
        (J := J) (K := K) F O₃)).IsRightAdjoint] :
    pullbackComparison (J := J) (K := K) F alpha ≫
        pullbackComparisonInv (J := J) (K := K) F alpha = 𝟙 _ := by
  exact comparison_hom_inv_id (J := J) (K := K) F
    (ringUnit (J := J) (K := K) F O₂)
    (ringUnit (J := J) (K := K) F O₃)
    (ringUnitSquare (J := J) (K := K) F alpha)

/-- The named inverse followed by the canonical pullback comparison is the identity. -/
@[simp, stacks 08TM "canonical conormal inverse comparison law"]
theorem pullbackComparison_inv_hom_id
    [RepresentablyFlat F] (alpha : O₂ ⟶ O₃)
    [(SheafOfModules.pushforward
      (structureMap
        (J := J) (K := K) F O₃)).IsRightAdjoint] :
    pullbackComparisonInv (J := J) (K := K) F alpha ≫
        pullbackComparison (J := J) (K := K) F alpha = 𝟙 _ := by
  exact comparison_inv_hom_id (J := J) (K := K) F
    (ringUnit (J := J) (K := K) F O₂)
    (ringUnit (J := J) (K := K) F O₃)
    (ringUnitSquare (J := J) (K := K) F alpha)

/-- The canonical conormal inverse-image comparison assembled from its named maps and inverse
laws. -/
@[stacks 08TM "canonical conormal inverse-image comparison isomorphism"]
noncomputable def pullbackComparisonIso
    [RepresentablyFlat F] (alpha : O₂ ⟶ O₃)
    [(SheafOfModules.pushforward
      (structureMap
        (J := J) (K := K) F O₃)).IsRightAdjoint] :
    (modulePullback
      (J := J) (K := K) F O₃).obj (conormalSource alpha) ≅
      conormalSource (pullbackMap F alpha) :=
  comparisonIso (J := J) (K := K) F
    (ringUnit (J := J) (K := K) F O₂)
    (ringUnit (J := J) (K := K) F O₃)
    (ringUnitSquare (J := J) (K := K) F alpha)

/-- Representable flatness makes the canonical conormal inverse-image comparison invertible. -/
@[stacks 08TM "canonical conormal inverse-image comparison is an isomorphism"]
instance pullbackComparison_isIso
    [RepresentablyFlat F] (alpha : O₂ ⟶ O₃)
    [(SheafOfModules.pushforward
      (structureMap
        (J := J) (K := K) F O₃)).IsRightAdjoint] :
    IsIso (pullbackComparison (J := J) (K := K) F alpha) := (pullbackComparisonIso (J := J) (K := K) F alpha).isIso_hom

/-- The forward map of `pullbackComparisonIso` is the canonical pullback comparison. -/
@[stacks 08TM "canonical conormal inverse-image comparison isomorphism hom", simp]
theorem pullbackComparisonIso_hom
    [RepresentablyFlat F] (alpha : O₂ ⟶ O₃)
    [(SheafOfModules.pushforward
      (structureMap
        (J := J) (K := K) F O₃)).IsRightAdjoint] :
    (pullbackComparisonIso (J := J) (K := K) F alpha).hom =
      pullbackComparison (J := J) (K := K) F alpha := rfl

/-- The inverse map of `pullbackComparisonIso` is the named pullback comparison inverse. -/
@[stacks 08TM "canonical conormal inverse-image comparison isomorphism inverse", simp]
theorem pullbackComparisonIso_inv
    [RepresentablyFlat F] (alpha : O₂ ⟶ O₃)
    [(SheafOfModules.pushforward
      (structureMap
        (J := J) (K := K) F O₃)).IsRightAdjoint] :
    (pullbackComparisonIso (J := J) (K := K) F alpha).inv =
      pullbackComparisonInv (J := J) (K := K) F alpha := rfl

end Canonical

end InverseImage
end Conormal
end RingedSite
end SheafOfModules
