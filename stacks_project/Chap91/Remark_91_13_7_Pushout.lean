/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient
public import stacks_project.Chap91.«91_10_5_1_TrivSqZeroExt»
public import stacks_project.Chap91.Lemma_91_13_6

/-!
# Pushout of a square-zero f⁻¹O_B-algebra extension along a coefficient map

In the identity-base setting of Lemma 91.13.6, the source constructs O'_1 by
pushing 0 ⟶ F ⟶ O_{C'} ⟶ O_C ⟶ 0 out along the adjunct of c : g^* F ⟶ G,
as the quotient of the fibre product (O_C ⊕ G) ×_{O_C} O_{C'} by the
antidiagonal of F.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open SheafOfModules.RingedSite.TrivSqZeroExt
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace Solution

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O_B O_C O_D : Sheaf J CommRingCat.{u}}
variable {fSharp : O_B ⟶ O_C} {gSharp : O_C ⟶ O_D}
variable {F : SheafOfModules (ringSheaf J O_C)}
variable {G : SheafOfModules (ringSheaf J O_D)}

/-- Objectwise identification of a sheaf-level pullback with the pullback of sections. -/
def pullbackAppIso {A B E : Sheaf J CommRingCat.{u}} (f : A ⟶ E) (g : B ⟶ E) (U : Cᵒᵖ) :
    (Limits.pullback f g).obj.obj U ≅ Limits.pullback (f.hom.app U) (g.hom.app U) :=
  ((CategoryTheory.evaluation (Cᵒᵖ) CommRingCat.{u}).obj U).mapIso
      (preservesLimitIso (sheafToPresheaf J CommRingCat.{u}) (cospan f g) ≪≫
        HasLimit.isoOfNatIso
          (cospanCompIso (sheafToPresheaf J CommRingCat.{u}) f g)) ≪≫
    pullbackObjIso f.hom g.hom U

/-- Pairing of compatible sections into a sheaf-level pullback. -/
def pullbackSectionMk {A B E : Sheaf J CommRingCat.{u}} (f : A ⟶ E) (g : B ⟶ E) (U : Cᵒᵖ)
    (a : A.obj.obj U) (b : B.obj.obj U) (h : f.hom.app U a = g.hom.app U b) :
    (Limits.pullback f g).obj.obj U :=
  (pullbackAppIso f g U).inv.hom
    ((IsLimit.conePointUniqueUpToIso
        (limit.isLimit (cospan (f.hom.app U) (g.hom.app U)))
        (CommRingCat.pullbackConeIsLimit (f.hom.app U) (g.hom.app U))).inv.hom
      ⟨(a, b), h⟩)

/-- The adjunct of `c : g^* F ⟶ G`, as a map `g⁻¹ F ⟶ G` of `g⁻¹ O_C`-modules. -/
def adjunctCoeff (c : (extendAlong gSharp).obj F ⟶ G) :
    F ⟶ (restrictionAlong gSharp).obj G :=
  (extendRestrictAdj gSharp).homEquiv F G c

/-- `adjunctCoeff` is the hom-equivalence of `extendRestrictAdj` at `c`. -/
theorem adjunctCoeff_spec (c : (extendAlong gSharp).obj F ⟶ G) :
    adjunctCoeff c = (extendRestrictAdj gSharp).homEquiv F G c := sorry

/-- The fibre product `(O_C ⊕ G) ×_{O_C} O_{C'}` of the trivial square-zero extension
by restriction of `G` with the original middle ring sheaf. -/
def pushoutProduct (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    Sheaf J CommRingCat.{u} :=
  Limits.pullback (fst O_C ((restrictionAlong gSharp).obj G)) SC.proj

/-- `pushoutProduct` is the pullback of `fst` along `SC.proj`. -/
theorem pushoutProduct_eq (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    pushoutProduct c SC =
      Limits.pullback (fst O_C ((restrictionAlong gSharp).obj G)) SC.proj := sorry

/-- Projection of the fibre product onto `O_C ⊕ G`. -/
def pushoutProduct_fst (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    pushoutProduct c SC ⟶ trivSqZeroExt O_C ((restrictionAlong gSharp).obj G) :=
  Limits.pullback.fst (fst O_C ((restrictionAlong gSharp).obj G)) SC.proj

/-- Projection of the fibre product onto `O_{C'}`. -/
def pushoutProduct_snd (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    pushoutProduct c SC ⟶ SC.middle :=
  Limits.pullback.snd (fst O_C ((restrictionAlong gSharp).obj G)) SC.proj

/-- The structure map of the fibre product onto `O_C`. -/
def pushoutProduct_toOC (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    pushoutProduct c SC ⟶ O_C :=
  pushoutProduct_fst c SC ≫ fst O_C ((restrictionAlong gSharp).obj G)

/-- Inclusion of a coefficient section of `F` as the antidiagonal generator
`(inr (adjunctCoeff c m), -ι(m))` in the fibre product. -/
def pushoutAntidiagonalSection (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (U : Cᵒᵖ) (m : F.val.obj U) : (pushoutProduct c SC).obj.obj U :=
  pullbackSectionMk (fst O_C ((restrictionAlong gSharp).obj G)) SC.proj U
    (inr O_C ((restrictionAlong gSharp).obj G) ((adjunctCoeff c).val.app U m))
    (- KernelIdeal.ιApp SC.proj U
        ((SC.proj_squareZero.targetModuleForgetIso SC.proj_quotient_isIso).hom.hom.app U
          ((SC.kernelIso.inv).val.app U m)))
    sorry

/-- The antidiagonal of `F` as a map of modules over the fibre product. -/
def pushoutAntidiagonalHom (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    (restrictionAlong (pushoutProduct_toOC c SC)).obj F ⟶
      unitModule J (pushoutProduct c SC) where
  val :=
    PresheafOfModules.homMk
      { app U :=
          AddCommGrpCat.ofHom <|
            AddMonoidHom.mk' (fun m ↦ pushoutAntidiagonalSection c SC U m) sorry
        naturality {_ _} _ := sorry }
      (fun _ _ _ ↦ sorry)

/-- The antidiagonal ideal sheaf of `F` in the fibre product. -/
def pushoutAntidiagonal (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    Subobject (unitModule J (pushoutProduct c SC)) :=
  imageSubobject (pushoutAntidiagonalHom c SC)

/-- `pushoutAntidiagonal` is the image of `pushoutAntidiagonalHom`. -/
theorem pushoutAntidiagonal_eq_image (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    pushoutAntidiagonal c SC = imageSubobject (pushoutAntidiagonalHom c SC) := sorry

/-- The antidiagonal of `F` is contained in the kernel of the fibre-product projection to `O_C`. -/
theorem pushoutAntidiagonal_le_ker (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    pushoutAntidiagonal c SC ≤ KernelIdeal.subobject (pushoutProduct_toOC c SC) := sorry

/-- The algebra pushout as the sheafified quotient of the fibre product by the antidiagonal. -/
def pushoutAlongSheaf (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    Sheaf J CommRingCat.{u} :=
  IdealSheaf.Quotient.sheaf (pushoutAntidiagonal c SC)

/-- The projection of the algebra pushout onto `O_C`. -/
def pushoutAlong_toOC (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    pushoutAlongSheaf c SC ⟶ O_C :=
  IdealSheaf.Quotient.lift (pushoutAntidiagonal c SC)
    (pushoutProduct_toOC c SC) (pushoutAntidiagonal_le_ker c SC)

/-- The structure map `O_B ⟶ O'_1` of the algebra pushout. -/
def pushoutAlong_fromOB (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    O_B ⟶ pushoutAlongSheaf c SC :=
  Limits.pullback.lift (fSharp ≫ inl O_C ((restrictionAlong gSharp).obj G)) SC.structureMap sorry ≫
    IdealSheaf.Quotient.projection (pushoutAntidiagonal c SC)

/-- The vertical map `O_{C'} ⟶ O'_1` of the source pushout square. -/
def pushoutAlong_fromMiddle (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    SC.middle ⟶ pushoutAlongSheaf c SC :=
  Limits.pullback.lift (SC.proj ≫ inl O_C ((restrictionAlong gSharp).obj G)) (𝟙 SC.middle) sorry ≫
    IdealSheaf.Quotient.projection (pushoutAntidiagonal c SC)

/-- The class of `(inr n, 0)` in the algebra pushout. -/
def pushoutAlong_inrSection (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (U : Cᵒᵖ) (n : G.val.obj U) :
    (pushoutAlongSheaf c SC).obj.obj U :=
  (IdealSheaf.Quotient.projection (pushoutAntidiagonal c SC)).hom.app U
    (pullbackSectionMk (fst O_C ((restrictionAlong gSharp).obj G)) SC.proj U
      (inr O_C ((restrictionAlong gSharp).obj G) n) 0 sorry)

/-- The projection `O'_1 ⟶ O_C` is locally surjective. -/
instance instIsLocallySurjective_pushoutAlong_toOC (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    Sheaf.IsLocallySurjective (pushoutAlong_toOC c SC) := sorry

/-- The projection `O'_1 ⟶ O_C` is a square-zero extension. -/
theorem isSquareZero_pushoutAlong_toOC (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    KernelIdeal.IsSquareZero (pushoutAlong_toOC c SC) := sorry

/-- The kernel section of the algebra pushout corresponding to a coefficient of `G`. -/
def kernelIso_pushoutAlong_invApp (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (U : Cᵒᵖ) (n : G.val.obj U) :
    ((isSquareZero_pushoutAlong_toOC c SC).targetModule
        (KernelIdeal.quotientComparison_isIso (pushoutAlong_toOC c SC))).val.obj U :=
  ((isSquareZero_pushoutAlong_toOC c SC).targetModuleForgetIso
        (KernelIdeal.quotientComparison_isIso (pushoutAlong_toOC c SC))).inv.hom.app U
    ((KernelIdeal.sectionsIso (pushoutAlong_toOC c SC) U).inv
      ⟨pushoutAlong_inrSection c SC U n, sorry⟩)

/-- The sectionwise lift of `pushoutProduct_toOC` through the antidiagonal quotient. -/
abbrev pushoutAlong_sectionLift (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (U : Cᵒᵖ) :
    IdealSheaf.Quotient.sections (pushoutAntidiagonal c SC) U ⟶ O_C.obj.obj U :=
  IdealSheaf.Quotient.sectionLift (pushoutAntidiagonal c SC)
    (pushoutProduct_toOC c SC) (pushoutAntidiagonal_le_ker c SC) U

/-- `pushoutAlong_sectionLift` is the sectionwise antidiagonal quotient eliminator. -/
theorem pushoutAlong_sectionLift_eq (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (U : Cᵒᵖ) :
    pushoutAlong_sectionLift c SC U =
      IdealSheaf.Quotient.sectionLift (pushoutAntidiagonal c SC)
        (pushoutProduct_toOC c SC) (pushoutAntidiagonal_le_ker c SC) U := sorry

/-- A presheaf class already in the kernel of `pushoutAlong_sectionLift`. -/
abbrev pushoutAlong_presheafKernelSection (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (U : Cᵒᵖ) :=
  RingHom.ker (pushoutAlong_sectionLift c SC U).hom

/-- Membership in `pushoutAlong_presheafKernelSection` is vanishing of `pushoutAlong_sectionLift`. -/
theorem mem_pushoutAlong_presheafKernelSection (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (U : Cᵒᵖ) (q : IdealSheaf.Quotient.sections (pushoutAntidiagonal c SC) U) :
    q ∈ pushoutAlong_presheafKernelSection c SC U ↔
      pushoutAlong_sectionLift c SC U q = 0 := sorry

/-- On a kernel class of `sectionLift`, `toOC (Quotient.out q) = 0` follows from
`sectionProjection_comp_sectionLift`. -/
theorem pushoutAlong_toOC_out_eq_zero (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (U : Cᵒᵖ) (q : pushoutAlong_presheafKernelSection c SC U) :
    (pushoutProduct_toOC c SC).hom.app U (Quotient.out q.1) = 0 := sorry

/-- The `G`-component of a presheaf class already in the kernel of `sectionLift`:
`snd(fst r) + adjunctCoeff(kernel of snd r)` on a `Quotient.out` representative. -/
def kernelIso_pushoutAlong_presheafHomApp (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (U : Cᵒᵖ) (q : pushoutAlong_presheafKernelSection c SC U) :
    ((restrictionAlong gSharp).obj G).val.obj U :=
  let r := Quotient.out q.1
  let hr := pushoutAlong_toOC_out_eq_zero c SC U q
  let hsnd :
      (pushoutProduct_snd c SC).hom.app U r ∈ RingHom.ker (SC.proj.hom.app U).hom :=
    RingHom.mem_ker.mpr
      ((congrArg (fun φ : pushoutProduct c SC ⟶ O_C => φ.hom.app U r)
          (Limits.pullback.condition :
            pushoutProduct_fst c SC ≫ fst O_C ((restrictionAlong gSharp).obj G) =
              pushoutProduct_snd c SC ≫ SC.proj)).symm.trans hr)
  snd O_C ((restrictionAlong gSharp).obj G) ((pushoutProduct_fst c SC).hom.app U r) +
    (adjunctCoeff c).val.app U
      ((SC.kernelIso.hom).val.app U
        ((SC.proj_squareZero.targetModuleForgetIso SC.proj_quotient_isIso).inv.hom.app U
          ((KernelIdeal.sectionsIso SC.proj U).inv
            ⟨(pushoutProduct_snd c SC).hom.app U r, hsnd⟩)))

/-- `kernelIso_pushoutAlong_presheafHomApp` is `snd(fst r) + adjunctCoeff(kernel of snd r)`
on `Quotient.out` of a kernel class of `sectionLift`. -/
theorem kernelIso_pushoutAlong_presheafHomApp_spec (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (U : Cᵒᵖ) (q : pushoutAlong_presheafKernelSection c SC U) :
    kernelIso_pushoutAlong_presheafHomApp c SC U q =
      (let r := Quotient.out q.1
      let hr := pushoutAlong_toOC_out_eq_zero c SC U q
      let hsnd :
          (pushoutProduct_snd c SC).hom.app U r ∈ RingHom.ker (SC.proj.hom.app U).hom :=
        RingHom.mem_ker.mpr
          ((congrArg (fun φ : pushoutProduct c SC ⟶ O_C => φ.hom.app U r)
              (Limits.pullback.condition :
                pushoutProduct_fst c SC ≫ fst O_C ((restrictionAlong gSharp).obj G) =
                  pushoutProduct_snd c SC ≫ SC.proj)).symm.trans hr)
      snd O_C ((restrictionAlong gSharp).obj G) ((pushoutProduct_fst c SC).hom.app U r) +
        (adjunctCoeff c).val.app U
          ((SC.kernelIso.hom).val.app U
            ((SC.proj_squareZero.targetModuleForgetIso SC.proj_quotient_isIso).inv.hom.app U
              ((KernelIdeal.sectionsIso SC.proj U).inv
                ⟨(pushoutProduct_snd c SC).hom.app U r, hsnd⟩)))) := sorry

/-- The presheaf of kernel classes of `pushoutAlong_sectionLift`. -/
def pushoutAlong_presheafKernel (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    Cᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (pushoutAlong_presheafKernelSection c SC U)
  map {U V} f :=
    AddCommGrpCat.ofHom <|
      AddMonoidHom.mk'
        (fun q ↦
          ⟨IdealSheaf.Quotient.restriction (pushoutAntidiagonal c SC) f q.1, sorry⟩) sorry
  map_id _ := sorry
  map_comp _ _ := sorry

/-- `pushoutAlong_presheafKernel` is objectwise the kernel of `pushoutAlong_sectionLift`. -/
theorem pushoutAlong_presheafKernel_obj (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (U : Cᵒᵖ) :
    (pushoutAlong_presheafKernel c SC).obj U =
      AddCommGrpCat.of (pushoutAlong_presheafKernelSection c SC U) := sorry

/-- Presheaf map sending a kernel class of `sectionLift` to its `G`-component. -/
def pushoutAlong_presheafKernelHom (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    pushoutAlong_presheafKernel c SC ⟶
      ((SheafOfModules.toSheaf (ringSheaf J O_C)).obj
        ((restrictionAlong gSharp).obj G)).obj where
  app U :=
    AddCommGrpCat.ofHom <|
      AddMonoidHom.mk' (kernelIso_pushoutAlong_presheafHomApp c SC U) sorry
  naturality {_ _} _ := sorry

/-- `pushoutAlong_presheafKernelHom` is `kernelIso_pushoutAlong_presheafHomApp` on each object. -/
theorem pushoutAlong_presheafKernelHom_app (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (U : Cᵒᵖ) (q : pushoutAlong_presheafKernelSection c SC U) :
    (pushoutAlong_presheafKernelHom c SC).app U q =
      kernelIso_pushoutAlong_presheafHomApp c SC U q := sorry

/-- The sheafification unit sends a kernel class of `sectionLift` into the kernel of
`pushoutAlong_toOC`. -/
theorem pushoutAlong_toSheafify_mem_ker (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (U : Cᵒᵖ) (q : pushoutAlong_presheafKernelSection c SC U) :
    (CategoryTheory.toSheafify J
        (IdealSheaf.Quotient.presheaf (pushoutAntidiagonal c SC))).app U q.1 ∈
      KernelIdeal.sectionIdeal (pushoutAlong_toOC c SC) U := sorry

/-- Inclusion of a kernel class of `sectionLift` into `KernelIdeal` of `pushoutAlong_toOC`,
via `toSheafify` of the antidiagonal quotient. -/
def pushoutAlong_presheafKernelι (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    pushoutAlong_presheafKernel c SC ⟶
      ((SheafOfModules.toSheaf (ringSheaf J (pushoutAlongSheaf c SC))).obj
        (KernelIdeal.sheaf (pushoutAlong_toOC c SC))).obj where
  app U :=
    AddCommGrpCat.ofHom <|
      AddMonoidHom.mk'
        (fun q ↦
          (KernelIdeal.sectionsIso (pushoutAlong_toOC c SC) U).inv
            ⟨(CategoryTheory.toSheafify J
                (IdealSheaf.Quotient.presheaf (pushoutAntidiagonal c SC))).app U q.1,
              pushoutAlong_toSheafify_mem_ker c SC U q⟩) sorry
  naturality {_ _} _ := sorry

/-- `pushoutAlong_presheafKernelι` sends a kernel class to the kernel-ideal preimage of its
`toSheafify` image. -/
theorem pushoutAlong_presheafKernelι_app (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (U : Cᵒᵖ) (q : pushoutAlong_presheafKernelSection c SC U) :
    (pushoutAlong_presheafKernelι c SC).app U q =
      (KernelIdeal.sectionsIso (pushoutAlong_toOC c SC) U).inv
        ⟨(CategoryTheory.toSheafify J
            (IdealSheaf.Quotient.presheaf (pushoutAntidiagonal c SC))).app U q.1,
          pushoutAlong_toSheafify_mem_ker c SC U q⟩ := sorry

/-- Sheafification of `pushoutAlong_presheafKernelHom`, as a map on the sheafified kernel
presheaf. -/
def pushoutAlong_presheafKernelSheafHom (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    CategoryTheory.sheafify J (pushoutAlong_presheafKernel c SC) ⟶
      ((SheafOfModules.toSheaf (ringSheaf J O_C)).obj
        ((restrictionAlong gSharp).obj G)).obj :=
  CategoryTheory.sheafifyLift J (pushoutAlong_presheafKernelHom c SC)
    ((SheafOfModules.toSheaf (ringSheaf J O_C)).obj
      ((restrictionAlong gSharp).obj G)).property

/-- `pushoutAlong_presheafKernelSheafHom` is the sheafification lift of
`pushoutAlong_presheafKernelHom`. -/
theorem pushoutAlong_presheafKernelSheafHom_eq (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    pushoutAlong_presheafKernelSheafHom c SC =
      CategoryTheory.sheafifyLift J (pushoutAlong_presheafKernelHom c SC)
        ((SheafOfModules.toSheaf (ringSheaf J O_C)).obj
          ((restrictionAlong gSharp).obj G)).property := sorry

/-- Sheafification of `pushoutAlong_presheafKernelι`, as a map from the sheafified kernel
presheaf to `KernelIdeal` of `pushoutAlong_toOC`. -/
def pushoutAlong_presheafKernelSheafι (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    CategoryTheory.sheafify J (pushoutAlong_presheafKernel c SC) ⟶
      ((SheafOfModules.toSheaf (ringSheaf J (pushoutAlongSheaf c SC))).obj
        (KernelIdeal.sheaf (pushoutAlong_toOC c SC))).obj :=
  CategoryTheory.sheafifyLift J (pushoutAlong_presheafKernelι c SC)
    ((SheafOfModules.toSheaf (ringSheaf J (pushoutAlongSheaf c SC))).obj
      (KernelIdeal.sheaf (pushoutAlong_toOC c SC))).property

/-- `pushoutAlong_presheafKernelSheafι` is the sheafification lift of
`pushoutAlong_presheafKernelι`. -/
theorem pushoutAlong_presheafKernelSheafι_eq (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    pushoutAlong_presheafKernelSheafι c SC =
      CategoryTheory.sheafifyLift J (pushoutAlong_presheafKernelι c SC)
        ((SheafOfModules.toSheaf (ringSheaf J (pushoutAlongSheaf c SC))).obj
          (KernelIdeal.sheaf (pushoutAlong_toOC c SC))).property := sorry

/-- Sheafifying the kernel of `sectionLift` recovers `KernelIdeal` of `pushoutAlong_toOC`. -/
theorem isIso_pushoutAlong_presheafKernelSheafι (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    IsIso (pushoutAlong_presheafKernelSheafι c SC) := sorry

/-- Identification of the sheafified kernel of `sectionLift` with `KernelIdeal` of
`pushoutAlong_toOC`. -/
def pushoutAlong_kernelPresheafIso (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    CategoryTheory.sheafify J (pushoutAlong_presheafKernel c SC) ≅
      ((SheafOfModules.toSheaf (ringSheaf J (pushoutAlongSheaf c SC))).obj
        (KernelIdeal.sheaf (pushoutAlong_toOC c SC))).obj :=
  @asIso _ _ _ _ (pushoutAlong_presheafKernelSheafι c SC)
    (isIso_pushoutAlong_presheafKernelSheafι c SC)

/-- The forward map of `pushoutAlong_kernelPresheafIso` is `pushoutAlong_presheafKernelSheafι`. -/
theorem pushoutAlong_kernelPresheafIso_hom (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    (pushoutAlong_kernelPresheafIso c SC).hom =
      pushoutAlong_presheafKernelSheafι c SC := sorry

/-- The `G`-component of a genuine kernel class of the sheafified antidiagonal quotient:
transport the kernel-presheaf formula along sheafification of the kernel of `sectionLift`. -/
def kernelIso_pushoutAlong_homApp (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (U : Cᵒᵖ)
    (x :
      ((isSquareZero_pushoutAlong_toOC c SC).targetModule
          (KernelIdeal.quotientComparison_isIso (pushoutAlong_toOC c SC))).val.obj U) :
    ((restrictionAlong gSharp).obj G).val.obj U :=
  let y :=
    ((isSquareZero_pushoutAlong_toOC c SC).targetModuleForgetIso
        (KernelIdeal.quotientComparison_isIso (pushoutAlong_toOC c SC))).hom.hom.app U x
  (pushoutAlong_presheafKernelSheafHom c SC).app U
    ((pushoutAlong_kernelPresheafIso c SC).inv.app U y)

/-- Kernel identification of the algebra pushout with the restricted coefficient module. -/
def kernelIso_pushoutAlong (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    (isSquareZero_pushoutAlong_toOC c SC).targetModule
        (KernelIdeal.quotientComparison_isIso (pushoutAlong_toOC c SC)) ≅
      (restrictionAlong gSharp).obj G where
  hom :=
    { val :=
        PresheafOfModules.homMk
          { app U :=
              AddCommGrpCat.ofHom <|
                AddMonoidHom.mk' (kernelIso_pushoutAlong_homApp c SC U) sorry
            naturality {_ _} _ := sorry }
          (fun _ _ _ ↦ sorry) }
  inv :=
    { val :=
        PresheafOfModules.homMk
          { app U :=
              AddCommGrpCat.ofHom <|
                AddMonoidHom.mk' (kernelIso_pushoutAlong_invApp c SC U) sorry
            naturality {_ _} _ := sorry }
          (fun _ _ _ ↦ sorry) }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward kernel identification is `kernelIso_pushoutAlong_homApp` on sections. -/
theorem kernelIso_pushoutAlong_hom_app (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (U : Cᵒᵖ)
    (x :
      ((isSquareZero_pushoutAlong_toOC c SC).targetModule
          (KernelIdeal.quotientComparison_isIso (pushoutAlong_toOC c SC))).val.obj U) :
    (kernelIso_pushoutAlong c SC).hom.val.app U x =
      kernelIso_pushoutAlong_homApp c SC U x := sorry

/-- Pushout of `0 ⟶ F ⟶ O_{C'} ⟶ O_C ⟶ 0` along the adjunct of `c`, as a square-zero
`f⁻¹ O_B`-algebra extension of `O_C` by the restriction of `G`. -/
def pushoutAlong (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp
      ((restrictionAlong gSharp).obj G)
      (zeroKernelMap fSharp ((restrictionAlong gSharp).obj G)) :=
  { middle := pushoutAlongSheaf c SC
    proj := pushoutAlong_toOC c SC
    structureMap := pushoutAlong_fromOB c SC
    proj_locallySurjective := instIsLocallySurjective_pushoutAlong_toOC c SC
    proj_squareZero := isSquareZero_pushoutAlong_toOC c SC
    proj_quotient_isIso := KernelIdeal.quotientComparison_isIso (pushoutAlong_toOC c SC)
    commutes := sorry
    kernelIso := kernelIso_pushoutAlong c SC
    induces_c := sorry }

/-- The carrier of `pushoutAlong` is the quotient of the fibre product by the antidiagonal. -/
theorem pushoutAlong_middle (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    (pushoutAlong c SC).middle =
      pushoutAlongSheaf c SC := sorry

/-- The projection of `pushoutAlong` is the quotient lift of the fibre-product map to `O_C`. -/
theorem pushoutAlong_proj (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    (pushoutAlong c SC).proj = pushoutAlong_toOC c SC := sorry

/-- The structure map of `pushoutAlong` is the composite of the fibre-product lift from `O_B`
with the quotient projection. -/
theorem pushoutAlong_structureMap (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    (pushoutAlong c SC).structureMap = pushoutAlong_fromOB c SC := sorry

/-- The identity-base connecting diagram from `O_{C'}` to the pushout along `c`. -/
def pushoutAlongDiagram (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    RelativeDiagram SC.proj (𝟙 O_B) (pushoutAlong c SC).proj (𝟙 O_B) :=
  RelativeDiagram.of fSharp SC.structureMap SC.commutes fSharp
    (pushoutAlong c SC).structureMap (pushoutAlong c SC).commutes
    (𝟙 O_C) (𝟙 O_B) (𝟙 O_B) rfl
    ((Category.id_comp fSharp).trans (Category.comp_id fSharp).symm)
    (kernelIdealHom SC ≫ adjunctCoeff c ≫
      (pushoutAlong c SC).kernelIso.inv ≫
        (idealTargetIso (pushoutAlong c SC)).inv ≫
          (SheafOfModules.Restriction.idIso' (ringSheafMap (𝟙 O_C))
            (ringSheafMap_id O_C)).hom.app (ideal (pushoutAlong c SC).proj))
    sorry

/-- `pushoutAlongDiagram` has identity maps on `O_B` and `O_C`, and `ν` is `adjunctCoeff`
transported along the kernel identifications. -/
theorem pushoutAlongDiagram_spec (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    (pushoutAlongDiagram c SC).g = 𝟙 O_C ∧
      (pushoutAlongDiagram c SC).t = 𝟙 O_B ∧
      (pushoutAlongDiagram c SC).t' = 𝟙 O_B := sorry

/-- The vertical map `O_{C'} ⟶ O'_1` in the source pushout square. -/
def toPushoutAlong (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    FittingMap (pushoutAlongDiagram c SC) :=
  FittingMap.of (pushoutAlong_fromMiddle c SC) sorry sorry sorry

/-- `toPushoutAlong` is the quotient of the fibre-product lift from `O_{C'}`. -/
theorem toPushoutAlong_hom (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    (toPushoutAlong c SC).hom = pushoutAlong_fromMiddle c SC := sorry


end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
