/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InverseImage
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension.Module
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Square

/-!
# Solutions of the first-order deformation equation on a ringed topos

After identifying underlying topoi, a first-order thickening of ringed topoi is a same-site
locally surjective square-zero morphism of commutative ring sheaves.  A solution of the
fixed extension diagram is a middle ring sheaf O' filling
`0 ⟶ G ⟶ O' ⟶ O ⟶ 0` over `0 ⟶ Ker π ⟶ O_{B'} ⟶ O_B ⟶ 0` so that the left vertical
arrow is the given map c of O_B-modules.

Inverse-image comparisons use the canonical library constructions. A further explicit-data
formulation can expose the preservation certificates of these inverse-image functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening

/-- Inverse image of a morphism of commutative ring sheaves along a continuous functor of sites. -/
abbrev inverseImageHom
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [HasWeakSheafify K CommRingCat.{w}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{w}, F.op.HasLeftKanExtension P]
    {O_B' O_B : Sheaf J CommRingCat.{w}} (π : O_B' ⟶ O_B) :
    (F.sheafPullback CommRingCat.{w} J K).obj O_B' ⟶
      (F.sheafPullback CommRingCat.{w} J K).obj O_B :=
  (F.sheafPullback CommRingCat.{w} J K).map π

/-- Inverse image of ring sheaves preserves composition. -/
theorem inverseImageHom_comp
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [HasWeakSheafify K CommRingCat.{w}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{w}, F.op.HasLeftKanExtension P]
    {O_B'' O_B' O_B : Sheaf J CommRingCat.{w}}
    (π : O_B'' ⟶ O_B') (σ : O_B' ⟶ O_B) :
    inverseImageHom J K F (π ≫ σ) =
      inverseImageHom J K F π ≫ inverseImageHom J K F σ := sorry

/-- The third term of `KernelIdeal.underlyingShortComplex π` is the additive sheaf of the
codomain ring sheaf. -/
noncomputable def underlyingTargetAdditiveIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    {A Q : Sheaf J CommRingCat.{w}} (π : A ⟶ Q) :
    KernelIdeal.underlyingTarget π ≅ KernelIdeal.underlyingUnit Q :=
  (SheafOfModules.toSheaf (ringSheaf J A)).mapIso
      ((SheafOfModules.ChangeOfRings.pushforwardIso (ringSheafMap π)).app
        (unitModule J Q)) ≪≫
    (SheafOfModules.restrictScalarsCompToSheaf (ringSheafMap π)).app (unitModule J Q)

/-- The kernel-ideal projection becomes the additive map of π after identifying the target
with the additive sheaf of the codomain ring. -/
theorem underlyingProjection_comp_underlyingTargetAdditiveIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    {A Q : Sheaf J CommRingCat.{w}} (π : A ⟶ Q) :
    KernelIdeal.underlyingProjection π ≫ (underlyingTargetAdditiveIso π).hom =
      SheafOfModules.unitUnderlyingMap (ringSheafMap π) := sorry

/-- Inverse image of commutative ring sheaves commutes with forgetting to additive sheaves. -/
noncomputable def inverseImageAdditiveIso
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [K.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [HasWeakSheafify K CommRingCat.{w}]
    [HasWeakSheafify K RingCat.{w}]
    [HasWeakSheafify K AddCommGrpCat.{w}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{w}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{w}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, F.op.HasLeftKanExtension P]
    [(forget₂ CommRingCat.{w} RingCat.{w}).PreservesLeftKanExtensions F.op]
    [(forget₂ RingCat.{w} AddCommGrpCat.{w}).PreservesLeftKanExtensions F.op]
    [K.PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.PreservesSheafification (forget₂ RingCat.{w} AddCommGrpCat.{w})] :
    F.sheafPullback CommRingCat.{w} J K ⋙
        sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w}) ⋙
        sheafCompose K (forget₂ RingCat.{w} AddCommGrpCat.{w}) ≅
      sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w}) ⋙
        sheafCompose J (forget₂ RingCat.{w} AddCommGrpCat.{w}) ⋙
        F.sheafPullback AddCommGrpCat.{w} J K :=
  Functor.isoWhiskerRight
      (Functor.sheafPullback.compSheafComposeIso F
        (forget₂ CommRingCat.{w} RingCat.{w}) J K)
      (sheafCompose K (forget₂ RingCat.{w} AddCommGrpCat.{w})) ≪≫
    Functor.isoWhiskerLeft
      (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w}))
      (Functor.sheafPullback.compSheafComposeIso F
        (forget₂ RingCat.{w} AddCommGrpCat.{w}) J K)

/-- The forgetful comparison intertwines inverse image of a ring-sheaf morphism with inverse
image of its underlying additive map. -/
theorem inverseImageAdditiveIso_hom_naturality
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [K.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [HasWeakSheafify K CommRingCat.{w}]
    [HasWeakSheafify K RingCat.{w}]
    [HasWeakSheafify K AddCommGrpCat.{w}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{w}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{w}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, F.op.HasLeftKanExtension P]
    [(forget₂ CommRingCat.{w} RingCat.{w}).PreservesLeftKanExtensions F.op]
    [(forget₂ RingCat.{w} AddCommGrpCat.{w}).PreservesLeftKanExtensions F.op]
    [K.PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.PreservesSheafification (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    {O_B' O_B : Sheaf J CommRingCat.{w}} (π : O_B' ⟶ O_B) :
    SheafOfModules.unitUnderlyingMap (ringSheafMap (inverseImageHom J K F π)) ≫
        (inverseImageAdditiveIso J K F).hom.app O_B =
      (inverseImageAdditiveIso J K F).hom.app O_B' ≫
        (F.sheafPullback AddCommGrpCat.{w} J K).map
          (SheafOfModules.unitUnderlyingMap (ringSheafMap π)) := sorry

/-- Inverse image identifies Ker(f⁻¹ t^♯) with f⁻¹(Ker t^♯), via the forgetful comparison of
CommRing and AddCommGrp pullbacks and preservation of kernels of the inverse image of t^♯. -/
noncomputable def kernelInverseImageIso
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [K.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [HasWeakSheafify K CommRingCat.{w}]
    [HasWeakSheafify K RingCat.{w}]
    [HasWeakSheafify K AddCommGrpCat.{w}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{w}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{w}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, F.op.HasLeftKanExtension P]
    [(forget₂ CommRingCat.{w} RingCat.{w}).PreservesLeftKanExtensions F.op]
    [(forget₂ RingCat.{w} AddCommGrpCat.{w}).PreservesLeftKanExtensions F.op]
    [K.PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.PreservesSheafification (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    {O_B' O_B : Sheaf J CommRingCat.{w}} (π : O_B' ⟶ O_B)
    [(F.sheafPullback AddCommGrpCat.{w} J K).PreservesZeroMorphisms]
    [PreservesLimit
      (parallelPair (SheafOfModules.unitUnderlyingMap (ringSheafMap π)) 0)
      (F.sheafPullback AddCommGrpCat.{w} J K)] :
    KernelIdeal.underlyingAdditive (inverseImageHom J K F π) ≅
      (F.sheafPullback AddCommGrpCat.{w} J K).obj
        (KernelIdeal.underlyingAdditive π) :=
  KernelIdeal.underlyingKernelIso (inverseImageHom J K F π) ≪≫
    kernel.mapIso
      (f := KernelIdeal.underlyingProjection (inverseImageHom J K F π))
      (SheafOfModules.unitUnderlyingMap (ringSheafMap (inverseImageHom J K F π)))
      (Iso.refl _) (underlyingTargetAdditiveIso (inverseImageHom J K F π)) rfl ≪≫
    kernel.mapIso
      (f := SheafOfModules.unitUnderlyingMap (ringSheafMap (inverseImageHom J K F π)))
      ((F.sheafPullback AddCommGrpCat.{w} J K).map
        (SheafOfModules.unitUnderlyingMap (ringSheafMap π)))
      ((inverseImageAdditiveIso J K F).app O_B')
      ((inverseImageAdditiveIso J K F).app O_B)
      ((inverseImageAdditiveIso J K F).hom.naturality π) ≪≫
    (PreservesKernel.iso (F.sheafPullback AddCommGrpCat.{w} J K)
      (SheafOfModules.unitUnderlyingMap (ringSheafMap π))).symm ≪≫
    (F.sheafPullback AddCommGrpCat.{w} J K).mapIso
      (kernel.mapIso
          (f := SheafOfModules.unitUnderlyingMap (ringSheafMap π))
          (KernelIdeal.underlyingProjection π) (Iso.refl _)
          (underlyingTargetAdditiveIso π).symm rfl ≪≫
        (KernelIdeal.underlyingKernelIso π).symm)

/-- The comparison identifies the kernel of f⁻¹(t^♯) with the inverse image of Ker(t^♯). -/
theorem kernelInverseImageIso_spec
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [K.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [HasWeakSheafify K CommRingCat.{w}]
    [HasWeakSheafify K RingCat.{w}]
    [HasWeakSheafify K AddCommGrpCat.{w}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{w}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{w}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, F.op.HasLeftKanExtension P]
    [(forget₂ CommRingCat.{w} RingCat.{w}).PreservesLeftKanExtensions F.op]
    [(forget₂ RingCat.{w} AddCommGrpCat.{w}).PreservesLeftKanExtensions F.op]
    [K.PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.PreservesSheafification (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    {O_B' O_B : Sheaf J CommRingCat.{w}} (π : O_B' ⟶ O_B)
    [(F.sheafPullback AddCommGrpCat.{w} J K).PreservesZeroMorphisms]
    [PreservesLimit
      (parallelPair (SheafOfModules.unitUnderlyingMap (ringSheafMap π)) 0)
      (F.sheafPullback AddCommGrpCat.{w} J K)] :
    (kernelInverseImageIso J K F π).hom ≫
        (F.sheafPullback AddCommGrpCat.{w} J K).map
          (KernelIdeal.underlyingInclusion π) =
      KernelIdeal.underlyingInclusion (inverseImageHom J K F π) ≫
        (inverseImageAdditiveIso J K F).hom.app O_B' := sorry

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable {O_B' O_B O : Sheaf J CommRingCat.{w}}
variable (π : O_B' ⟶ O_B) [Sheaf.IsLocallySurjective π]

/-- The known bottom row 0 ⟶ Ker π ⟶ O_{B'} ⟶ O_B ⟶ 0 of additive sheaves. -/
abbrev bottomShortComplex : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  KernelIdeal.underlyingShortComplex π

/-- The base extension is short exact. -/
theorem bottomShortComplex_shortExact : (bottomShortComplex π).ShortExact :=
  KernelIdeal.underlyingShortComplex_shortExact π

variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (hπ : KernelIdeal.IsSquareZero π)
variable (fSharp : O_B ⟶ O)
variable (G : SheafOfModules (ringSheaf J O))
variable (c :
    hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
      (restrictionAlong fSharp).obj G)

/-- The composite of the kernel inclusion of π with the additive map of a commuting
structure map is killed by the projection of the unknown thickening. -/
theorem kernelMap_lift_zero {middle : Sheaf J CommRingCat.{w}}
    (proj : middle ⟶ O) (structureMap : O_B' ⟶ middle)
    (hcomm : structureMap ≫ proj = π ≫ fSharp) :
    (kernel.ι (KernelIdeal.underlyingProjection π) ≫
        SheafOfModules.unitUnderlyingMap (ringSheafMap structureMap)) ≫
      KernelIdeal.underlyingProjection proj = 0 := sorry

/-- The additive sheaf map of kernels induced by a commuting structure map. -/
noncomputable def kernelAdditiveMap {middle : Sheaf J CommRingCat.{w}}
    (proj : middle ⟶ O) (hproj : KernelIdeal.IsSquareZero proj)
    (hproj_iso : IsIso (KernelIdeal.quotientComparison proj))
    (structureMap : O_B' ⟶ middle)
    (hcomm : structureMap ≫ proj = π ≫ fSharp) :
    (SheafOfModules.toSheaf (ringSheaf J O_B)).obj
        (hπ.targetModule (KernelIdeal.quotientComparison_isIso π)) ⟶
      (SheafOfModules.toSheaf (ringSheaf J O)).obj (hproj.targetModule hproj_iso) :=
  (hπ.targetModuleForgetIso (KernelIdeal.quotientComparison_isIso π)).hom ≫
    (KernelIdeal.underlyingKernelIso π).hom ≫
      kernel.lift (KernelIdeal.underlyingProjection proj)
        (kernel.ι (KernelIdeal.underlyingProjection π) ≫
          SheafOfModules.unitUnderlyingMap (ringSheafMap structureMap))
        (kernelMap_lift_zero π fSharp proj structureMap hcomm) ≫
      (KernelIdeal.underlyingKernelIso proj).inv ≫
        (hproj.targetModuleForgetIso hproj_iso).inv

/-- The O_B-module map on kernels induced by a commuting structure map. -/
noncomputable def kernelMapOf {middle : Sheaf J CommRingCat.{w}}
    (proj : middle ⟶ O) (hproj : KernelIdeal.IsSquareZero proj)
    (hproj_iso : IsIso (KernelIdeal.quotientComparison proj))
    (structureMap : O_B' ⟶ middle)
    (hcomm : structureMap ≫ proj = π ≫ fSharp) :
    hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
      (restrictionAlong fSharp).obj (hproj.targetModule hproj_iso) where
  val :=
    PresheafOfModules.homMk
      ((sheafToPresheaf J AddCommGrpCat.{w}).map
        (kernelAdditiveMap π hπ fSharp proj hproj hproj_iso structureMap hcomm))
      (fun _ _ _ ↦ sorry)

/-- A solution of the fixed extension diagram: a middle ring sheaf O' with a first-order projection onto O,
a structure map from O_{B'}, a kernel identification with G, and the induced map on kernels
equal to c. -/
structure Solution where
  /-- The unknown middle ring sheaf O'. -/
  middle : Sheaf J CommRingCat.{w}
  /-- The square-zero locally surjective projection O' ⟶ O. -/
  proj : middle ⟶ O
  /-- The structure map (f')^♯ : O_{B'} ⟶ O'. -/
  structureMap : O_B' ⟶ middle
  /-- The projection O' ⟶ O is locally surjective. -/
  proj_locallySurjective : Sheaf.IsLocallySurjective proj
  /-- The kernel ideal of the projection O' ⟶ O is square zero. -/
  proj_squareZero : KernelIdeal.IsSquareZero proj
  /-- The first isomorphism theorem for the locally surjective projection O' ⟶ O. -/
  proj_quotient_isIso : IsIso (KernelIdeal.quotientComparison proj)
  /-- The right-hand square of ring sheaves commutes. -/
  commutes : structureMap ≫ proj = π ≫ fSharp
  /-- Identification of Ker(proj) with G as O-modules. -/
  kernelIso : proj_squareZero.targetModule proj_quotient_isIso ≅ G
  /-- The induced map on kernels equals c. -/
  induces_c :
    kernelMapOf π hπ fSharp proj proj_squareZero proj_quotient_isIso
        structureMap commutes ≫
      (restrictionAlong fSharp).map kernelIso.hom = c

/-- Assemble a solution from a middle ring sheaf, its structure maps, a kernel identification,
and the induced-map condition. -/
def Solution.ofMaps (middle : Sheaf J CommRingCat.{w}) (proj : middle ⟶ O)
    (structureMap : O_B' ⟶ middle)
    (proj_locallySurjective : Sheaf.IsLocallySurjective proj)
    (proj_squareZero : KernelIdeal.IsSquareZero proj)
    (proj_quotient_isIso : IsIso (KernelIdeal.quotientComparison proj))
    (commutes : structureMap ≫ proj = π ≫ fSharp)
    (kernelIso : proj_squareZero.targetModule proj_quotient_isIso ≅ G)
    (induces_c :
      kernelMapOf π hπ fSharp proj proj_squareZero proj_quotient_isIso
          structureMap commutes ≫
        (restrictionAlong fSharp).map kernelIso.hom = c) :
    Solution π hπ fSharp G c where
  middle := middle
  proj := proj
  structureMap := structureMap
  proj_locallySurjective := proj_locallySurjective
  proj_squareZero := proj_squareZero
  proj_quotient_isIso := proj_quotient_isIso
  commutes := commutes
  kernelIso := kernelIso
  induces_c := induces_c

variable {π hπ fSharp G c}

/-- The top row 0 ⟶ Ker(proj) ⟶ O' ⟶ O ⟶ 0 of additive sheaves. -/
abbrev topShortComplex (S : Solution π hπ fSharp G c) :
    ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  KernelIdeal.underlyingShortComplex S.proj

/-- The top row of a solution is short exact. -/
theorem topShortComplex_shortExact (S : Solution π hπ fSharp G c) :
    (topShortComplex S).ShortExact := sorry

/-- The O_B-module map on kernels induced by a solution. -/
noncomputable def kernelMap (S : Solution π hπ fSharp G c) :
    hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
      (restrictionAlong fSharp).obj
        (S.proj_squareZero.targetModule S.proj_quotient_isIso) :=
  kernelMapOf π hπ fSharp S.proj S.proj_squareZero S.proj_quotient_isIso
    S.structureMap S.commutes

/-- The filled additive diagram of a solution, as a morphism of short complexes. -/
noncomputable def toHom (S : Solution π hπ fSharp G c) :
    (bottomShortComplex π).Hom (topShortComplex S) where
  τ₁ :=
    (hπ.targetModuleForgetIso (KernelIdeal.quotientComparison_isIso π)).inv ≫
      kernelAdditiveMap π hπ fSharp S.proj S.proj_squareZero S.proj_quotient_isIso
          S.structureMap S.commutes ≫
        (S.proj_squareZero.targetModuleForgetIso S.proj_quotient_isIso).hom
  τ₂ := SheafOfModules.unitUnderlyingMap (ringSheafMap S.structureMap)
  τ₃ :=
    (underlyingTargetAdditiveIso π).hom ≫
      SheafOfModules.unitUnderlyingMap (ringSheafMap fSharp) ≫
        (underlyingTargetAdditiveIso S.proj).inv
  comm₁₂ := sorry
  comm₂₃ := sorry

/-- A solution is a first-order thickening of O whose structure map from O_{B'} commutes with π
and f^♯ and induces c on kernels. -/
theorem spec (S : Solution π hπ fSharp G c) :
    Sheaf.IsLocallySurjective S.proj ∧
      KernelIdeal.IsSquareZero S.proj ∧
        S.structureMap ≫ S.proj = π ≫ fSharp ∧
          kernelMap S ≫ (restrictionAlong fSharp).map S.kernelIso.hom = c := sorry

/-- The identification of kernels induces the given map c. -/
theorem induces_c_eq (S : Solution π hπ fSharp G c) :
    kernelMap S ≫ (restrictionAlong fSharp).map S.kernelIso.hom = c := sorry

/-- The two squares of `toHom` commute. -/
theorem toHom_comm (S : Solution π hπ fSharp G c) :
    (toHom S).τ₁ ≫ (topShortComplex S).f = (bottomShortComplex π).f ≫ (toHom S).τ₂ ∧
      (toHom S).τ₂ ≫ (topShortComplex S).g = (bottomShortComplex π).g ≫ (toHom S).τ₃ :=
  sorry

/-- Forgetting the O-module structure, `kernelIso` identifies G with the kernel ideal of
`proj`. -/
noncomputable def kernelIso_forget (S : Solution π hπ fSharp G c) :
    (SheafOfModules.toSheaf (ringSheaf J O)).obj G ≅
      KernelIdeal.underlyingAdditive S.proj :=
  (SheafOfModules.toSheaf (ringSheaf J O)).mapIso S.kernelIso.symm ≪≫
    S.proj_squareZero.targetModuleForgetIso S.proj_quotient_isIso

/-- The same-site morphism of ringed topoi associated to a morphism of commutative ring
sheaves on C, after identifying underlying topoi. -/
noncomputable def sameSiteToposHom
    [J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    {O₁ O₂ : Sheaf J CommRingCat.{w}} (α : O₂ ⟶ O₁) :
    RingedSite.ToposHom (RingedSite.ofCommRingSheaf J O₁)
      (RingedSite.ofCommRingSheaf J O₂) where
  toTopos := MorphismOfTopoiIn.id J
  structureMap :=
    MorphismOfTopoiIn.ringInverseImageIdIso.hom.app (ringSheaf J O₂) ≫
      ringSheafMap α

/-- The identity-underlying-topos commutative square of the fixed extension diagram
on C. This is not the original morphism of thickenings (f, f') when f changes topoi. -/
noncomputable def toCommSquare
    [J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    (S : Solution π hπ fSharp G c) :
    RingedSite.ToposHom.CommSquare
      (RingedSite.ofCommRingSheaf J O)
      (RingedSite.ofCommRingSheaf J S.middle)
      (RingedSite.ofCommRingSheaf J O_B)
      (RingedSite.ofCommRingSheaf J O_B') where
  upper := sameSiteToposHom S.proj
  left := sameSiteToposHom fSharp
  right := sameSiteToposHom S.structureMap
  lower := sameSiteToposHom π
  cell :=
    { homIso := Iso.refl _
      comm := sorry }

end SheafOfModules.RingedSite.FirstOrderThickening
