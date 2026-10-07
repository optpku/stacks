module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient
public import stacks_project.Chap91.Lemma_91_14_3_Extension

/-!
# Pushout of identity-base square-zero f⁻¹𝒪_B-algebra extensions along a coefficient map

The source functor F sends 0 ⟶ ℱ ⟶ 𝒪' ⟶ 𝒪_X ⟶ 0 to the extension of 𝒪_X by 𝒢
obtained as the quotient of the fibre product (𝒪_X ⊕ 𝒢) ×_{𝒪_X} 𝒪' by the
antidiagonal of ℱ along φ : ℱ ⟶ 𝒢, as in Remark 91.13.7 with g = id.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.TrivSqZeroExt (trivSqZeroExt fst inl snd inr)
open AlgebraicGeometry.AlgebraicSpace.Hom.SquareZeroAlgebraExtension

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.SquareZeroAlgebraExtension

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} {f : X ⟶ B}
variable {ℱ 𝒢 : X.Modules}

/-- Objectwise identification of a sheaf-level pullback with the pullback of sections. -/
def pullbackAppIso {R T Q : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (p : R ⟶ Q) (q : T ⟶ Q) (U : (smallEtaleSite X)ᵒᵖ) :
    (Limits.pullback p q).obj.obj U ≅ Limits.pullback (p.hom.app U) (q.hom.app U) :=
  ((CategoryTheory.evaluation ((smallEtaleSite X)ᵒᵖ) CommRingCat.{u}).obj U).mapIso
      (preservesLimitIso
          (sheafToPresheaf (smallEtaleTopology X) CommRingCat.{u}) (cospan p q) ≪≫
        HasLimit.isoOfNatIso
          (cospanCompIso (sheafToPresheaf (smallEtaleTopology X) CommRingCat.{u}) p q)) ≪≫
    pullbackObjIso p.hom q.hom U

/-- Pairing of compatible sections into a sheaf-level pullback. -/
def pullbackSectionMk {R T Q : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (p : R ⟶ Q) (q : T ⟶ Q) (U : (smallEtaleSite X)ᵒᵖ)
    (a : R.obj.obj U) (b : T.obj.obj U) (h : p.hom.app U a = q.hom.app U b) :
    (Limits.pullback p q).obj.obj U :=
  (pullbackAppIso p q U).inv.hom
    ((IsLimit.conePointUniqueUpToIso
        (limit.isLimit (cospan (p.hom.app U) (q.hom.app U)))
        (CommRingCat.pullbackConeIsLimit (p.hom.app U) (q.hom.app U))).inv.hom
      ⟨(a, b), h⟩)

/-- The fibre product `(𝒪_X ⊕ 𝒢) ×_{𝒪_X} 𝒪'` of the trivial square-zero extension by 𝒢
with the original middle ring sheaf. -/
def pushoutProduct (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  Limits.pullback (fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢)) E.proj

/-- Projection of the fibre product onto `𝒪_X ⊕ 𝒢`. -/
def pushoutProduct_fst (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    pushoutProduct φ E ⟶ trivSqZeroExt.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢) :=
  Limits.pullback.fst (fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢)) E.proj

/-- Projection of the fibre product onto 𝒪'. -/
def pushoutProduct_snd (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    pushoutProduct φ E ⟶ E.middle :=
  Limits.pullback.snd (fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢)) E.proj

/-- The structure map of the fibre product onto 𝒪_X. -/
def pushoutProduct_toOX (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    pushoutProduct φ E ⟶ commStructureSheaf X :=
  pushoutProduct_fst φ E ≫ fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢)

/-- Inclusion of a coefficient section of ℱ as the antidiagonal generator
`(inr (φ m), -ι(kernelIso.inv m))` in the fibre product. -/
def pushoutAntidiagonalSection (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (m : ((toCommModules X).obj ℱ).val.obj U) :
    (pushoutProduct φ E).obj.obj U :=
  pullbackSectionMk (fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢)) E.proj U
    (inr.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢)
      (((toCommModules X).map φ).val.app U m))
    (- KernelIdeal.ιApp E.proj U
        ((E.proj_squareZero.targetModuleForgetIso E.proj_quotient_isIso).hom.hom.app U
          ((E.kernelIso.inv).val.app U m)))
    sorry

/-- The antidiagonal of ℱ as a map of modules over the fibre product. -/
def pushoutAntidiagonalHom (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (restrictionAlong (pushoutProduct_toOX φ E)).obj ((toCommModules X).obj ℱ) ⟶
      unitModule (smallEtaleTopology X) (pushoutProduct φ E) where
  val :=
    PresheafOfModules.homMk
      { app U :=
          AddCommGrpCat.ofHom <|
            AddMonoidHom.mk' (fun m ↦ pushoutAntidiagonalSection φ E U m) sorry
        naturality {_ _} _ := sorry }
      (fun _ _ _ ↦ sorry)

/-- The antidiagonal morphism has an image in the module category of the fibre product. -/
instance hasImage_pushoutAntidiagonalHom (φ : ℱ ⟶ 𝒢)
    (E : SquareZeroAlgebraExtension f ℱ) :
    HasImage (pushoutAntidiagonalHom φ E) :=
  sorry

/-- The antidiagonal ideal sheaf of ℱ in the fibre product. -/
def pushoutAntidiagonal (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    Subobject (unitModule (smallEtaleTopology X) (pushoutProduct φ E)) :=
  imageSubobject (pushoutAntidiagonalHom φ E)

/-- The antidiagonal of ℱ is contained in the kernel of the fibre-product projection to 𝒪_X. -/
theorem pushoutAntidiagonal_le_ker (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    pushoutAntidiagonal φ E ≤ KernelIdeal.subobject (pushoutProduct_toOX φ E) :=
  sorry

/-- The algebra pushout as the sheafified quotient of the fibre product by the antidiagonal. -/
def pushoutSheaf (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  IdealSheaf.Quotient.sheaf.{u + 1, u, u} (pushoutAntidiagonal φ E)

/-- The projection of the algebra pushout onto 𝒪_X. -/
def pushout_toOX (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    pushoutSheaf φ E ⟶ commStructureSheaf X :=
  IdealSheaf.Quotient.lift.{u + 1, u, u} (pushoutAntidiagonal φ E)
    (pushoutProduct_toOX φ E) (pushoutAntidiagonal_le_ker φ E)

/-- The structure map f⁻¹𝒪_B ⟶ 𝒪'_pushout of the algebra pushout. -/
def pushout_fromOB (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    commInverseImageStructureSheaf f ⟶ pushoutSheaf φ E :=
  Limits.pullback.lift
      (commInverseImageStructureSheafMap f ≫
        inl.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢))
      E.structureMap sorry ≫
    IdealSheaf.Quotient.projection.{u + 1, u, u} (pushoutAntidiagonal φ E)

/-- The vertical map 𝒪' ⟶ 𝒪'_pushout of the source pushout square. -/
def pushout_fromMiddle (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    E.middle ⟶ pushoutSheaf φ E :=
  Limits.pullback.lift
      (E.proj ≫ inl.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢))
      (𝟙 E.middle) sorry ≫
    IdealSheaf.Quotient.projection.{u + 1, u, u} (pushoutAntidiagonal φ E)

/-- The class of `(inr n, 0)` in the algebra pushout. -/
def pushout_inrSection (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (n : ((toCommModules X).obj 𝒢).val.obj U) :
    (pushoutSheaf φ E).obj.obj U :=
  (IdealSheaf.Quotient.projection.{u + 1, u, u} (pushoutAntidiagonal φ E)).hom.app U
    (pullbackSectionMk (fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢)) E.proj U
      (inr.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢) n) 0 sorry)

/-- The projection of the algebra pushout onto 𝒪_X is locally surjective. -/
instance instIsLocallySurjective_pushout_toOX (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    Sheaf.IsLocallySurjective (pushout_toOX φ E) :=
  sorry

/-- The projection of the algebra pushout onto 𝒪_X is a square-zero extension. -/
theorem isSquareZero_pushout_toOX (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    KernelIdeal.IsSquareZero (pushout_toOX φ E) :=
  sorry

/-- The kernel section of the algebra pushout corresponding to a coefficient of 𝒢. -/
def kernelIso_pushout_invApp (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (n : ((toCommModules X).obj 𝒢).val.obj U) :
    ((isSquareZero_pushout_toOX φ E).targetModule
        (KernelIdeal.quotientComparison_isIso (pushout_toOX φ E))).val.obj U :=
  ((isSquareZero_pushout_toOX φ E).targetModuleForgetIso
        (KernelIdeal.quotientComparison_isIso (pushout_toOX φ E))).inv.hom.app U
    ((KernelIdeal.sectionsIso.{u + 1, u, u} (pushout_toOX φ E) U).inv
      ⟨pushout_inrSection φ E U n, sorry⟩)

/-- The sectionwise lift of `pushoutProduct_toOX` through the antidiagonal quotient. -/
abbrev pushout_sectionLift (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) :
    IdealSheaf.Quotient.sections.{u + 1, u, u} (pushoutAntidiagonal φ E) U ⟶
      (commStructureSheaf X).obj.obj U :=
  IdealSheaf.Quotient.sectionLift.{u + 1, u, u} (pushoutAntidiagonal φ E)
    (pushoutProduct_toOX φ E) (pushoutAntidiagonal_le_ker φ E) U

/-- `pushout_sectionLift` is the sectionwise antidiagonal quotient eliminator. -/
theorem pushout_sectionLift_eq (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) :
    pushout_sectionLift φ E U =
      IdealSheaf.Quotient.sectionLift.{u + 1, u, u} (pushoutAntidiagonal φ E)
        (pushoutProduct_toOX φ E) (pushoutAntidiagonal_le_ker φ E) U :=
  sorry

/-- A presheaf class already in the kernel of `pushout_sectionLift`. -/
abbrev pushout_presheafKernelSection (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) :=
  RingHom.ker (pushout_sectionLift φ E U).hom

/-- Membership in `pushout_presheafKernelSection` is vanishing of `pushout_sectionLift`. -/
theorem mem_pushout_presheafKernelSection (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ)
    (q : IdealSheaf.Quotient.sections.{u + 1, u, u} (pushoutAntidiagonal φ E) U) :
    q ∈ pushout_presheafKernelSection φ E U ↔ pushout_sectionLift φ E U q = 0 :=
  sorry

/-- On a kernel class of `sectionLift`, `toOX (Quotient.out q) = 0`. -/
theorem pushout_toOX_out_eq_zero (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (q : pushout_presheafKernelSection φ E U) :
    (pushoutProduct_toOX φ E).hom.app U (Quotient.out q.1) = 0 :=
  sorry

/-- The 𝒢-component of a presheaf class already in the kernel of `sectionLift`:
`snd(fst r) + φ(kernel of snd r)` on a `Quotient.out` representative. -/
def kernelIso_pushout_presheafHomApp (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (q : pushout_presheafKernelSection φ E U) :
    ((toCommModules X).obj 𝒢).val.obj U :=
  let r := Quotient.out q.1
  let hr := pushout_toOX_out_eq_zero φ E U q
  let hsnd :
      (pushoutProduct_snd φ E).hom.app U r ∈ RingHom.ker (E.proj.hom.app U).hom :=
    RingHom.mem_ker.mpr
      ((congrArg (fun ψ : pushoutProduct φ E ⟶ commStructureSheaf X => ψ.hom.app U r)
          (Limits.pullback.condition :
            pushoutProduct_fst φ E ≫
                fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢) =
              pushoutProduct_snd φ E ≫ E.proj)).symm.trans hr)
  snd.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢)
      ((pushoutProduct_fst φ E).hom.app U r) +
    ((toCommModules X).map φ).val.app U
      ((E.kernelIso.hom).val.app U
        ((E.proj_squareZero.targetModuleForgetIso E.proj_quotient_isIso).inv.hom.app U
          ((KernelIdeal.sectionsIso E.proj U).inv
            ⟨(pushoutProduct_snd φ E).hom.app U r, hsnd⟩)))

/-- `kernelIso_pushout_presheafHomApp` is `snd(fst r) + φ(kernel of snd r)`. -/
theorem kernelIso_pushout_presheafHomApp_spec (φ : ℱ ⟶ 𝒢)
    (E : SquareZeroAlgebraExtension f ℱ) (U : (smallEtaleSite X)ᵒᵖ)
    (q : pushout_presheafKernelSection φ E U) :
    kernelIso_pushout_presheafHomApp φ E U q =
      (let r := Quotient.out q.1
      let hr := pushout_toOX_out_eq_zero φ E U q
      let hsnd :
          (pushoutProduct_snd φ E).hom.app U r ∈ RingHom.ker (E.proj.hom.app U).hom :=
        RingHom.mem_ker.mpr
          ((congrArg (fun ψ : pushoutProduct φ E ⟶ commStructureSheaf X => ψ.hom.app U r)
              (Limits.pullback.condition :
                pushoutProduct_fst φ E ≫
                    fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢) =
                  pushoutProduct_snd φ E ≫ E.proj)).symm.trans hr)
      snd.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢)
          ((pushoutProduct_fst φ E).hom.app U r) +
        ((toCommModules X).map φ).val.app U
          ((E.kernelIso.hom).val.app U
            ((E.proj_squareZero.targetModuleForgetIso E.proj_quotient_isIso).inv.hom.app U
              ((KernelIdeal.sectionsIso E.proj U).inv
                ⟨(pushoutProduct_snd φ E).hom.app U r, hsnd⟩)))) :=
  sorry

/-- The presheaf of kernel classes of `pushout_sectionLift`. -/
def pushout_presheafKernel (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (pushout_presheafKernelSection φ E U)
  map {U V} g :=
    AddCommGrpCat.ofHom <|
      AddMonoidHom.mk'
        (fun q ↦
          ⟨IdealSheaf.Quotient.restriction.{u + 1, u, u} (pushoutAntidiagonal φ E) g q.1, sorry⟩)
        sorry
  map_id _ := sorry
  map_comp _ _ := sorry

/-- `pushout_presheafKernel` is objectwise the kernel of `pushout_sectionLift`. -/
theorem pushout_presheafKernel_obj (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (pushout_presheafKernel φ E).obj U =
      AddCommGrpCat.of (pushout_presheafKernelSection φ E U) :=
  sorry

/-- Presheaf map sending a kernel class of `sectionLift` to its 𝒢-component. -/
def pushout_presheafKernelHom (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    pushout_presheafKernel φ E ⟶
      ((SheafOfModules.toSheaf
          (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (commStructureSheaf X))).obj
        ((toCommModules X).obj 𝒢)).obj where
  app U :=
    AddCommGrpCat.ofHom <|
      AddMonoidHom.mk' (kernelIso_pushout_presheafHomApp φ E U) sorry
  naturality {_ _} _ := sorry

/-- `pushout_presheafKernelHom` is `kernelIso_pushout_presheafHomApp` on each object. -/
theorem pushout_presheafKernelHom_app (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (q : pushout_presheafKernelSection φ E U) :
    (pushout_presheafKernelHom φ E).app U q =
      kernelIso_pushout_presheafHomApp φ E U q :=
  sorry

/-- The sheafification unit sends a kernel class of `sectionLift` into the kernel of
`pushout_toOX`. -/
theorem pushout_toSheafify_mem_ker (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (q : pushout_presheafKernelSection φ E U) :
    (CategoryTheory.toSheafify (smallEtaleTopology X)
        (IdealSheaf.Quotient.presheaf.{u + 1, u, u} (pushoutAntidiagonal φ E))).app U q.1 ∈
      KernelIdeal.sectionIdeal (pushout_toOX φ E) U :=
  sorry

/-- Inclusion of a kernel class of `sectionLift` into the kernel ideal of the antidiagonal
quotient. -/
def pushout_presheafKernelι (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    pushout_presheafKernel φ E ⟶
      ((SheafOfModules.toSheaf (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (pushoutSheaf φ E))).obj
        (KernelIdeal.sheaf.{u + 1, u, u} (pushout_toOX φ E))).obj where
  app U :=
    AddCommGrpCat.ofHom <|
      AddMonoidHom.mk'
        (fun q ↦
          (KernelIdeal.sectionsIso.{u + 1, u, u} (pushout_toOX φ E) U).inv
            ⟨(CategoryTheory.toSheafify (smallEtaleTopology X)
                (IdealSheaf.Quotient.presheaf.{u + 1, u, u} (pushoutAntidiagonal φ E))).app U q.1,
              pushout_toSheafify_mem_ker φ E U q⟩) sorry
  naturality {_ _} _ := sorry

/-- `pushout_presheafKernelι` sends a kernel class to the kernel-ideal preimage of its
`toSheafify` image. -/
theorem pushout_presheafKernelι_app (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (q : pushout_presheafKernelSection φ E U) :
    (pushout_presheafKernelι φ E).app U q =
      (KernelIdeal.sectionsIso.{u + 1, u, u} (pushout_toOX φ E) U).inv
        ⟨(CategoryTheory.toSheafify (smallEtaleTopology X)
            (IdealSheaf.Quotient.presheaf.{u + 1, u, u} (pushoutAntidiagonal φ E))).app U q.1,
          pushout_toSheafify_mem_ker φ E U q⟩ :=
  sorry

/-- Sheafification of `pushout_presheafKernelHom`, as a map on the sheafified kernel
presheaf. -/
def pushout_presheafKernelSheafHom (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    CategoryTheory.sheafify (smallEtaleTopology X) (pushout_presheafKernel φ E) ⟶
      ((SheafOfModules.toSheaf
          (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (commStructureSheaf X))).obj
        ((toCommModules X).obj 𝒢)).obj :=
  CategoryTheory.sheafifyLift (smallEtaleTopology X) (pushout_presheafKernelHom φ E)
    ((SheafOfModules.toSheaf
        (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (commStructureSheaf X))).obj
      ((toCommModules X).obj 𝒢)).property

/-- `pushout_presheafKernelSheafHom` is the sheafification lift of
`pushout_presheafKernelHom`. -/
theorem pushout_presheafKernelSheafHom_eq (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    pushout_presheafKernelSheafHom φ E =
      CategoryTheory.sheafifyLift (smallEtaleTopology X) (pushout_presheafKernelHom φ E)
        ((SheafOfModules.toSheaf
            (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (commStructureSheaf X))).obj
          ((toCommModules X).obj 𝒢)).property :=
  sorry

/-- Sheafification of `pushout_presheafKernelι`, as a map from the sheafified kernel
presheaf to `KernelIdeal` of `pushout_toOX`. -/
def pushout_presheafKernelSheafι (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    CategoryTheory.sheafify (smallEtaleTopology X) (pushout_presheafKernel φ E) ⟶
      ((SheafOfModules.toSheaf (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (pushoutSheaf φ E))).obj
        (KernelIdeal.sheaf.{u + 1, u, u} (pushout_toOX φ E))).obj :=
  CategoryTheory.sheafifyLift (smallEtaleTopology X) (pushout_presheafKernelι φ E)
    ((SheafOfModules.toSheaf (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (pushoutSheaf φ E))).obj
      (KernelIdeal.sheaf.{u + 1, u, u} (pushout_toOX φ E))).property

/-- `pushout_presheafKernelSheafι` is the sheafification lift of `pushout_presheafKernelι`. -/
theorem pushout_presheafKernelSheafι_eq (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    pushout_presheafKernelSheafι φ E =
      CategoryTheory.sheafifyLift (smallEtaleTopology X) (pushout_presheafKernelι φ E)
        ((SheafOfModules.toSheaf (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (pushoutSheaf φ E))).obj
          (KernelIdeal.sheaf.{u + 1, u, u} (pushout_toOX φ E))).property :=
  sorry

/-- Sheafifying the kernel of `sectionLift` recovers `KernelIdeal` of `pushout_toOX`. -/
theorem isIso_pushout_presheafKernelSheafι (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    IsIso (pushout_presheafKernelSheafι φ E) :=
  sorry

/-- Identification of the sheafified kernel of `sectionLift` with `KernelIdeal` of
`pushout_toOX`. -/
def pushout_kernelPresheafIso (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    CategoryTheory.sheafify (smallEtaleTopology X) (pushout_presheafKernel φ E) ≅
      ((SheafOfModules.toSheaf (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (pushoutSheaf φ E))).obj
        (KernelIdeal.sheaf.{u + 1, u, u} (pushout_toOX φ E))).obj :=
  @asIso _ _ _ _ (pushout_presheafKernelSheafι φ E) (isIso_pushout_presheafKernelSheafι φ E)

/-- The forward map of `pushout_kernelPresheafIso` is `pushout_presheafKernelSheafι`. -/
theorem pushout_kernelPresheafIso_hom (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (pushout_kernelPresheafIso φ E).hom = pushout_presheafKernelSheafι φ E :=
  sorry

/-- The 𝒢-component of a genuine kernel class of the sheafified antidiagonal quotient. -/
def kernelIso_pushout_homApp (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ)
    (x : ((isSquareZero_pushout_toOX φ E).targetModule
        (KernelIdeal.quotientComparison_isIso (pushout_toOX φ E))).val.obj U) :
    ((toCommModules X).obj 𝒢).val.obj U :=
  let y :=
    ((isSquareZero_pushout_toOX φ E).targetModuleForgetIso
        (KernelIdeal.quotientComparison_isIso (pushout_toOX φ E))).hom.hom.app U x
  (pushout_presheafKernelSheafHom φ E).app U ((pushout_kernelPresheafIso φ E).inv.app U y)

/-- Kernel identification of the algebra pushout with 𝒢. -/
def kernelIso_pushout (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (isSquareZero_pushout_toOX φ E).targetModule
        (KernelIdeal.quotientComparison_isIso (pushout_toOX φ E)) ≅
      (toCommModules X).obj 𝒢 where
  hom :=
    { val :=
        PresheafOfModules.homMk
          { app U :=
              AddCommGrpCat.ofHom <|
                AddMonoidHom.mk' (kernelIso_pushout_homApp φ E U) sorry
            naturality {_ _} _ := sorry }
          (fun _ _ _ ↦ sorry) }
  inv :=
    { val :=
        PresheafOfModules.homMk
          { app U :=
              AddCommGrpCat.ofHom <|
                AddMonoidHom.mk' (kernelIso_pushout_invApp φ E U) sorry
            naturality {_ _} _ := sorry }
          (fun _ _ _ ↦ sorry) }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward kernel identification is `kernelIso_pushout_homApp` on sections. -/
theorem kernelIso_pushout_hom_app (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ)
    (x : ((isSquareZero_pushout_toOX φ E).targetModule
        (KernelIdeal.quotientComparison_isIso (pushout_toOX φ E))).val.obj U) :
    (kernelIso_pushout φ E).hom.val.app U x = kernelIso_pushout_homApp φ E U x :=
  sorry

/-- The inverse kernel identification is `kernelIso_pushout_invApp` on sections. -/
theorem kernelIso_pushout_inv_app (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (n : ((toCommModules X).obj 𝒢).val.obj U) :
    (kernelIso_pushout φ E).inv.val.app U n = kernelIso_pushout_invApp φ E U n :=
  sorry

/-- Pushout of `0 ⟶ ℱ ⟶ 𝒪' ⟶ 𝒪_X ⟶ 0` along φ, as a square-zero f⁻¹𝒪_B-algebra
extension of 𝒪_X by 𝒢. -/
def pushout (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    SquareZeroAlgebraExtension f 𝒢 where
  middle := pushoutSheaf φ E
  proj := pushout_toOX φ E
  structureMap := pushout_fromOB φ E
  proj_locallySurjective := instIsLocallySurjective_pushout_toOX φ E
  proj_squareZero := isSquareZero_pushout_toOX φ E
  proj_quotient_isIso := KernelIdeal.quotientComparison_isIso (pushout_toOX φ E)
  commutes := sorry
  kernelIso := kernelIso_pushout φ E

/-- The carrier of `pushout φ E` is the antidiagonal quotient of the fibre product. -/
theorem pushout_middle (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (pushout φ E).middle = pushoutSheaf φ E :=
  sorry

/-- The projection of `pushout φ E` is the quotient lift of the fibre-product map to 𝒪_X. -/
theorem pushout_proj (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (pushout φ E).proj = pushout_toOX φ E :=
  sorry

/-- The structure map of `pushout φ E` is the composite of the fibre-product lift from
f⁻¹𝒪_B with the quotient projection. -/
theorem pushout_structureMap (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (pushout φ E).structureMap = pushout_fromOB φ E :=
  sorry

/-- The kernel identification of `pushout φ E` is `kernelIso_pushout`. -/
theorem pushout_kernelIso (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (pushout φ E).kernelIso = kernelIso_pushout φ E :=
  sorry

/-- The ring-sheaf map of fibre products induced by a morphism of extensions. -/
def pushoutProduct_map (φ : ℱ ⟶ 𝒢) {E₁ E₂ : SquareZeroAlgebraExtension f ℱ} (α : Hom E₁ E₂) :
    pushoutProduct φ E₁ ⟶ pushoutProduct φ E₂ :=
  Limits.pullback.lift (pushoutProduct_fst φ E₁)
    (pushoutProduct_snd φ E₁ ≫ α.hom) sorry

/-- The ring-sheaf map of algebra pushouts induced by a morphism of extensions. -/
def pushout_map (φ : ℱ ⟶ 𝒢) {E₁ E₂ : SquareZeroAlgebraExtension f ℱ} (α : Hom E₁ E₂) :
    pushoutSheaf φ E₁ ⟶ pushoutSheaf φ E₂ :=
  IdealSheaf.Quotient.lift.{u + 1, u, u} (pushoutAntidiagonal φ E₁)
    (pushoutProduct_map φ α ≫ IdealSheaf.Quotient.projection.{u + 1, u, u} (pushoutAntidiagonal φ E₂))
    sorry

/-- The morphism `pushout φ E₁ ⟶ pushout φ E₂` induced by a morphism of extensions. -/
def pushoutHom (φ : ℱ ⟶ 𝒢) {E₁ E₂ : SquareZeroAlgebraExtension f ℱ} (α : Hom E₁ E₂) :
    Hom (pushout φ E₁) (pushout φ E₂) where
  hom := pushout_map φ α
  comm_proj := sorry
  comm_structure := sorry
  induces_id := sorry

/-- The source functor F, sending an identity-base square-zero f⁻¹𝒪_B-algebra extension
of 𝒪_X by ℱ to the pushout along φ : ℱ ⟶ 𝒢. -/
def pushoutFunctor (f : X ⟶ B) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    SquareZeroAlgebraExtension f ℱ ⥤ SquareZeroAlgebraExtension f 𝒢 where
  obj := pushout φ
  map α := pushoutHom φ α
  map_id := sorry
  map_comp := sorry

/-- On objects, `pushoutFunctor f φ` is `pushout φ`. -/
theorem pushoutFunctor_obj (f : X ⟶ B) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢)
    (E : SquareZeroAlgebraExtension f ℱ) :
    (pushoutFunctor f φ).obj E = pushout φ E :=
  sorry

/-- On morphisms, `pushoutFunctor f φ` is `pushoutHom φ`. -/
theorem pushoutFunctor_map (f : X ⟶ B) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢)
    {E₁ E₂ : SquareZeroAlgebraExtension f ℱ} (α : Hom E₁ E₂) :
    (pushoutFunctor f φ).map α = pushoutHom φ α :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.SquareZeroAlgebraExtension
