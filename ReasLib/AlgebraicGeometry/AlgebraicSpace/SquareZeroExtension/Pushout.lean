module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension
public import ReasLib.CategoryTheory.Sites.LocalIsoDescent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Pushout of identity-base square-zero f⁻¹𝒪_B-algebra extensions along a coefficient map

Coefficient pushout sends 0 ⟶ ℱ ⟶ 𝒪' ⟶ 𝒪_X ⟶ 0 to the extension of 𝒪_X by 𝒢
obtained as the quotient of the fibre product (𝒪_X ⊕ 𝒢) ×_{𝒪_X} 𝒪' by the
antidiagonal of ℱ along φ : ℱ ⟶ 𝒢.
-/

@[expose] public section

-- Transparent constructions refer to private section functions and their proof laws.
-- This export-elaboration option preserves those implementation details as private.
set_option backward.privateInPublic true

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
private def pullbackAppIso {R T Q : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (p : R ⟶ Q) (q : T ⟶ Q) (U : (smallEtaleSite X)ᵒᵖ) :
    (Limits.pullback p q).obj.obj U ≅ Limits.pullback (p.hom.app U) (q.hom.app U) :=
  ((CategoryTheory.evaluation ((smallEtaleSite X)ᵒᵖ) CommRingCat.{u}).obj U).mapIso
      (preservesLimitIso
          (sheafToPresheaf (smallEtaleTopology X) CommRingCat.{u}) (cospan p q) ≪≫
        HasLimit.isoOfNatIso
          (cospanCompIso (sheafToPresheaf (smallEtaleTopology X) CommRingCat.{u}) p q)) ≪≫
    pullbackObjIso p.hom q.hom U

/-- Pairing of compatible sections into a sheaf-level pullback. -/
private def pullbackSectionMk {R T Q : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
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

private theorem pushoutAntidiagonalSection_compatible (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (m : ((toCommModules X).obj ℱ).val.obj U) :
    (fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢)).hom.app U
      (inr.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢)
        (((toCommModules X).map φ).val.app U m)) =
    E.proj.hom.app U
      (- KernelIdeal.ιApp E.proj U
        ((E.proj_squareZero.targetModuleForgetIso E.proj_quotient_isIso).hom.hom.app U
          (E.kernelIso.inv.val.app U m))) := by
  sorry

/-- Inclusion of a coefficient section of ℱ as the antidiagonal generator
`(inr (φ m), -ι(kernelIso.inv m))` in the fibre product. -/
private def pushoutAntidiagonalSection (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (m : ((toCommModules X).obj ℱ).val.obj U) :
    (pushoutProduct φ E).obj.obj U :=
  pullbackSectionMk (fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢)) E.proj U
    (inr.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢)
      (((toCommModules X).map φ).val.app U m))
    (- KernelIdeal.ιApp E.proj U
        ((E.proj_squareZero.targetModuleForgetIso E.proj_quotient_isIso).hom.hom.app U
          ((E.kernelIso.inv).val.app U m)))
    (pushoutAntidiagonalSection_compatible φ E U m)

private theorem pushoutAntidiagonalHom_laws (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (∀ U (x y : ((restrictionAlong (pushoutProduct_toOX φ E)).obj ((toCommModules X).obj ℱ)).val.obj U), pushoutAntidiagonalSection φ E U (x + y) = pushoutAntidiagonalSection φ E U x + pushoutAntidiagonalSection φ E U y) ∧
    (∀ {U V} (g : U ⟶ V) (x : ((restrictionAlong (pushoutProduct_toOX φ E)).obj ((toCommModules X).obj ℱ)).val.obj U),
      pushoutAntidiagonalSection φ E V (((restrictionAlong (pushoutProduct_toOX φ E)).obj ((toCommModules X).obj ℱ)).val.map g x) = (unitModule (smallEtaleTopology X) (pushoutProduct φ E)).val.map g (pushoutAntidiagonalSection φ E U x)) ∧
    (∀ U (r : (pushoutProduct φ E).obj.obj U) (x : ((restrictionAlong (pushoutProduct_toOX φ E)).obj ((toCommModules X).obj ℱ)).val.obj U),
      pushoutAntidiagonalSection φ E U (r • x) = r • pushoutAntidiagonalSection φ E U x) := by
  sorry

/-- The antidiagonal coefficient map into the fibre product. -/
def pushoutAntidiagonalHom (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) : ((restrictionAlong (pushoutProduct_toOX φ E)).obj ((toCommModules X).obj ℱ)) ⟶ (unitModule (smallEtaleTopology X) (pushoutProduct φ E)) where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom <| AddMonoidHom.mk' (pushoutAntidiagonalSection φ E U)
        ((pushoutAntidiagonalHom_laws φ E).1 U)
      naturality {U V} g := by
        ext x
        exact (pushoutAntidiagonalHom_laws φ E).2.1 g x }
    (fun U r x ↦ (pushoutAntidiagonalHom_laws φ E).2.2 U r x)

/-- The antidiagonal ideal sheaf of ℱ in the fibre product. -/
def pushoutAntidiagonal (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    Subobject (unitModule (smallEtaleTopology X) (pushoutProduct φ E)) :=
  imageSubobject (pushoutAntidiagonalHom φ E)

/-- The antidiagonal of ℱ is contained in the kernel of the fibre-product projection to 𝒪_X. -/
private theorem pushoutAntidiagonal_le_ker (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
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
      E.structureMap (by
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun h ↦ commInverseImageStructureSheafMap f ≫ h)
            (SheafOfModules.RingedSite.TrivSqZeroExt.fst_comp_inl
              (commStructureSheaf X) ((toCommModules X).obj 𝒢))).trans
            ((Category.comp_id _).trans E.commutes.symm))) ≫
    IdealSheaf.Quotient.projection.{u + 1, u, u} (pushoutAntidiagonal φ E)

/-- The vertical map 𝒪' ⟶ 𝒪'_pushout of the coefficient-pushout square. -/
def pushout_fromMiddle (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    E.middle ⟶ pushoutSheaf φ E :=
  Limits.pullback.lift
      (E.proj ≫ inl.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢))
      (𝟙 E.middle) (by
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun h ↦ E.proj ≫ h)
            (SheafOfModules.RingedSite.TrivSqZeroExt.fst_comp_inl
              (commStructureSheaf X) ((toCommModules X).obj 𝒢))).trans
            ((Category.comp_id _).trans (Category.id_comp _).symm))) ≫
    IdealSheaf.Quotient.projection.{u + 1, u, u} (pushoutAntidiagonal φ E)

/-- The class of `(inr n, 0)` in the algebra pushout. -/
def pushout_inrSection (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (n : ((toCommModules X).obj 𝒢).val.obj U) :
    (pushoutSheaf φ E).obj.obj U :=
  (IdealSheaf.Quotient.projection.{u + 1, u, u} (pushoutAntidiagonal φ E)).hom.app U
    (pullbackSectionMk (fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢)) E.proj U
      (inr.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢) n) 0 (by exact (map_zero (E.proj.hom.app U).hom).symm))

/-- The projection of the algebra pushout onto 𝒪_X is locally surjective. -/
theorem isLocallySurjective_pushout_toOX (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    Sheaf.IsLocallySurjective (pushout_toOX φ E) :=
  sorry

/-- The quotient of the coefficient pushout by the kernel of its projection is isomorphic
 to the structure sheaf. -/
def pushout_quotient_isIso (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    IsIso (KernelIdeal.quotientComparison (pushout_toOX φ E)) :=
  @KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _ (pushout_toOX φ E)
    (smallEtaleTopology_wEqualsLocallyBijective_commRingCat X)
    (isLocallySurjective_pushout_toOX φ E)

/-- The projection of the algebra pushout onto 𝒪_X is a square-zero extension. -/
theorem isSquareZero_pushout_toOX (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    KernelIdeal.IsSquareZero (pushout_toOX φ E) :=
  sorry

private theorem pushout_inrSection_mem_kernel (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (n : ((toCommModules X).obj 𝒢).val.obj U) :
    pushout_inrSection φ E U n ∈ KernelIdeal.sectionIdeal (pushout_toOX φ E) U := by
  sorry

/-- The kernel section of the algebra pushout corresponding to a coefficient of 𝒢. -/
private def kernelIso_pushout_invApp (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (n : ((toCommModules X).obj 𝒢).val.obj U) :
    ((isSquareZero_pushout_toOX φ E).targetModule
        (pushout_quotient_isIso φ E)).val.obj U :=
  ((isSquareZero_pushout_toOX φ E).targetModuleForgetIso
        (pushout_quotient_isIso φ E)).inv.hom.app U
    ((KernelIdeal.sectionsIso.{u + 1, u, u} (pushout_toOX φ E) U).inv
      ⟨pushout_inrSection φ E U n, pushout_inrSection_mem_kernel φ E U n⟩)

/-- The sectionwise lift of `pushoutProduct_toOX` through the antidiagonal quotient. -/
private abbrev pushout_sectionLift (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) :
    IdealSheaf.Quotient.sections.{u + 1, u, u} (pushoutAntidiagonal φ E) U ⟶
      (commStructureSheaf X).obj.obj U :=
  IdealSheaf.Quotient.sectionLift.{u + 1, u, u} (pushoutAntidiagonal φ E)
    (pushoutProduct_toOX φ E) (pushoutAntidiagonal_le_ker φ E) U

/-- `pushout_sectionLift` is the sectionwise antidiagonal quotient eliminator. -/
private theorem pushout_sectionLift_eq (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) :
    pushout_sectionLift φ E U =
      IdealSheaf.Quotient.sectionLift.{u + 1, u, u} (pushoutAntidiagonal φ E)
        (pushoutProduct_toOX φ E) (pushoutAntidiagonal_le_ker φ E) U :=
  rfl

/-- A presheaf class already in the kernel of `pushout_sectionLift`. -/
private abbrev pushout_presheafKernelSection (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) :=
  RingHom.ker (pushout_sectionLift φ E U).hom

/-- Membership in `pushout_presheafKernelSection` is vanishing of `pushout_sectionLift`. -/
private theorem mem_pushout_presheafKernelSection (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ)
    (q : IdealSheaf.Quotient.sections.{u + 1, u, u} (pushoutAntidiagonal φ E) U) :
    q ∈ pushout_presheafKernelSection φ E U ↔ pushout_sectionLift φ E U q = 0 :=
  Iff.rfl

/-- On a kernel class of `sectionLift`, `toOX (Quotient.out q) = 0`. -/
private theorem pushout_toOX_out_eq_zero (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (q : pushout_presheafKernelSection φ E U) :
    (pushoutProduct_toOX φ E).hom.app U (Quotient.out q.1) = 0 :=
  sorry

/-- The 𝒢-component of a presheaf class already in the kernel of `sectionLift`:
`snd(fst r) + φ(kernel of snd r)` on a `Quotient.out` representative. -/
private def kernelIso_pushout_presheafHomApp (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
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
private theorem kernelIso_pushout_presheafHomApp_spec (φ : ℱ ⟶ 𝒢)
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
  rfl

private theorem pushout_presheafKernel_laws (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    ∀ {U V : (smallEtaleSite X)ᵒᵖ} (g : U ⟶ V) (q : (pushout_presheafKernelSection φ E U)),
      IdealSheaf.Quotient.restriction.{u + 1, u, u} (pushoutAntidiagonal φ E) g q.1 ∈ pushout_presheafKernelSection φ E V := by
  sorry

private def pushout_presheafKernel (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (pushout_presheafKernelSection φ E U)
  map {U V} g := AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun q ↦ ⟨IdealSheaf.Quotient.restriction.{u + 1, u, u} (pushoutAntidiagonal φ E) g q.1, pushout_presheafKernel_laws φ E g q⟩)
      (by intro x y; apply Subtype.ext; exact map_add (IdealSheaf.Quotient.restriction.{u + 1, u, u} (pushoutAntidiagonal φ E) g).hom _ _)
  map_id U := by
    ext q
    exact congrArg (fun h ↦ h q.1) (IdealSheaf.Quotient.restriction_id (pushoutAntidiagonal φ E) U)
  map_comp g h := by
    ext q
    exact congrArg (fun k ↦ k q.1) (IdealSheaf.Quotient.restriction_comp (pushoutAntidiagonal φ E) g h)

/-- `pushout_presheafKernel` is objectwise the kernel of `pushout_sectionLift`. -/
private theorem pushout_presheafKernel_obj (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (pushout_presheafKernel φ E).obj U =
      AddCommGrpCat.of (pushout_presheafKernelSection φ E U) :=
  rfl

private theorem pushout_presheafKernelHom_laws (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (∀ U (x y : (pushout_presheafKernel φ E).obj U),
      kernelIso_pushout_presheafHomApp φ E U (x + y) =
        kernelIso_pushout_presheafHomApp φ E U x + kernelIso_pushout_presheafHomApp φ E U y) ∧
    (∀ {U V} (g : U ⟶ V) (x : (pushout_presheafKernel φ E).obj U),
      kernelIso_pushout_presheafHomApp φ E V ((pushout_presheafKernel φ E).map g x) =
        (((SheafOfModules.toSheaf
      (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (commStructureSheaf X))).obj
    ((toCommModules X).obj 𝒢)).obj).map g (kernelIso_pushout_presheafHomApp φ E U x)) := by
  sorry

private def pushout_presheafKernelHom (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    pushout_presheafKernel φ E ⟶ ((SheafOfModules.toSheaf
      (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (commStructureSheaf X))).obj
    ((toCommModules X).obj 𝒢)).obj where
  app U := AddCommGrpCat.ofHom <|
    AddMonoidHom.mk' (kernelIso_pushout_presheafHomApp φ E U)
      ((pushout_presheafKernelHom_laws φ E).1 U)
  naturality {U V} g := by
    ext x
    exact (pushout_presheafKernelHom_laws φ E).2 g x

/-- `pushout_presheafKernelHom` is `kernelIso_pushout_presheafHomApp` on each object. -/
private theorem pushout_presheafKernelHom_app (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (q : pushout_presheafKernelSection φ E U) :
    (pushout_presheafKernelHom φ E).app U q =
      kernelIso_pushout_presheafHomApp φ E U q :=
  rfl

/-- The sheafification unit sends a kernel class of `sectionLift` into the kernel of
`pushout_toOX`. -/
private theorem pushout_toSheafify_mem_ker (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (q : pushout_presheafKernelSection φ E U) :
    (CategoryTheory.toSheafify (smallEtaleTopology X)
        (IdealSheaf.Quotient.presheaf.{u + 1, u, u} (pushoutAntidiagonal φ E))).app U q.1 ∈
      KernelIdeal.sectionIdeal (pushout_toOX φ E) U :=
  sorry

private def pushout_presheafKernelιApp (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) (U : (smallEtaleSite X)ᵒᵖ)
    (q : (pushout_presheafKernel φ E).obj U) : (((SheafOfModules.toSheaf
      (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (pushoutSheaf φ E))).obj
    (KernelIdeal.sheaf.{u + 1, u, u} (pushout_toOX φ E))).obj).obj U :=
  (KernelIdeal.sectionsIso.{u + 1, u, u} (pushout_toOX φ E) U).inv
            ⟨(CategoryTheory.toSheafify (smallEtaleTopology X)
                (IdealSheaf.Quotient.presheaf.{u + 1, u, u} (pushoutAntidiagonal φ E))).app U q.1,
              pushout_toSheafify_mem_ker φ E U q⟩

private theorem pushout_presheafKernelι_laws (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (∀ U (x y : (pushout_presheafKernel φ E).obj U),
      pushout_presheafKernelιApp φ E U (x + y) =
        pushout_presheafKernelιApp φ E U x + pushout_presheafKernelιApp φ E U y) ∧
    (∀ {U V} (g : U ⟶ V) (x : (pushout_presheafKernel φ E).obj U),
      pushout_presheafKernelιApp φ E V ((pushout_presheafKernel φ E).map g x) =
        (((SheafOfModules.toSheaf
      (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (pushoutSheaf φ E))).obj
    (KernelIdeal.sheaf.{u + 1, u, u} (pushout_toOX φ E))).obj).map g (pushout_presheafKernelιApp φ E U x)) := by
  sorry

private def pushout_presheafKernelι (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    pushout_presheafKernel φ E ⟶ ((SheafOfModules.toSheaf
      (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (pushoutSheaf φ E))).obj
    (KernelIdeal.sheaf.{u + 1, u, u} (pushout_toOX φ E))).obj where
  app U := AddCommGrpCat.ofHom <|
    AddMonoidHom.mk' (pushout_presheafKernelιApp φ E U)
      ((pushout_presheafKernelι_laws φ E).1 U)
  naturality {U V} g := by
    ext x
    exact (pushout_presheafKernelι_laws φ E).2 g x

/-- `pushout_presheafKernelι` sends a kernel class to the kernel-ideal preimage of its
`toSheafify` image. -/
private theorem pushout_presheafKernelι_app (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (q : pushout_presheafKernelSection φ E U) :
    (pushout_presheafKernelι φ E).app U q =
      (KernelIdeal.sectionsIso.{u + 1, u, u} (pushout_toOX φ E) U).inv
        ⟨(CategoryTheory.toSheafify (smallEtaleTopology X)
            (IdealSheaf.Quotient.presheaf.{u + 1, u, u} (pushoutAntidiagonal φ E))).app U q.1,
          pushout_toSheafify_mem_ker φ E U q⟩ :=
  rfl

private theorem pushout_presheafKernelι_locallyBijective (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    Presheaf.IsLocallySurjective (smallEtaleTopology X)
      (Functor.whiskerRight (pushout_presheafKernelι φ E) (forget AddCommGrpCat.{u})) ∧
    Presheaf.IsLocallyInjective (smallEtaleTopology X)
      (Functor.whiskerRight (pushout_presheafKernelι φ E) (forget AddCommGrpCat.{u})) := by
  sorry

/-- The 𝒢-component of a genuine kernel class of the sheafified antidiagonal quotient. -/
private def kernelIso_pushout_homApp (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ)
    (x : ((isSquareZero_pushout_toOX φ E).targetModule
        (pushout_quotient_isIso φ E)).val.obj U) :
    ((toCommModules X).obj 𝒢).val.obj U :=
  let y :=
    ((isSquareZero_pushout_toOX φ E).targetModuleForgetIso
        (pushout_quotient_isIso φ E)).hom.hom.app U x
  Presheaf.LocalIsoDescent.app (smallEtaleTopology X)
    (Functor.whiskerRight (pushout_presheafKernelι φ E) (forget AddCommGrpCat.{u}))
    (Functor.whiskerRight (pushout_presheafKernelHom φ E) (forget AddCommGrpCat.{u}))
    (hηs := (pushout_presheafKernelι_locallyBijective φ E).1)
    (hηi := (pushout_presheafKernelι_locallyBijective φ E).2)
    ((sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u})).obj
      ((SheafOfModules.toSheaf
        (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (commStructureSheaf X))).obj
          ((toCommModules X).obj 𝒢))).property y

private theorem kernelIso_pushout_hom_laws (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (∀ U (x y : ((isSquareZero_pushout_toOX φ E).targetModule (pushout_quotient_isIso φ E)).val.obj U), kernelIso_pushout_homApp φ E U (x + y) = kernelIso_pushout_homApp φ E U x + kernelIso_pushout_homApp φ E U y) ∧
    (∀ {U V} (g : U ⟶ V) (x : ((isSquareZero_pushout_toOX φ E).targetModule (pushout_quotient_isIso φ E)).val.obj U),
      kernelIso_pushout_homApp φ E V (((isSquareZero_pushout_toOX φ E).targetModule (pushout_quotient_isIso φ E)).val.map g x) = ((toCommModules X).obj 𝒢).val.map g (kernelIso_pushout_homApp φ E U x)) ∧
    (∀ U (r : (commStructureSheaf X).obj.obj U) (x : ((isSquareZero_pushout_toOX φ E).targetModule (pushout_quotient_isIso φ E)).val.obj U),
      kernelIso_pushout_homApp φ E U (r • x) = r • kernelIso_pushout_homApp φ E U x) := by
  sorry

private def kernelIso_pushout_hom (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) : ((isSquareZero_pushout_toOX φ E).targetModule (pushout_quotient_isIso φ E)) ⟶ ((toCommModules X).obj 𝒢) where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom <| AddMonoidHom.mk' (kernelIso_pushout_homApp φ E U)
        ((kernelIso_pushout_hom_laws φ E).1 U)
      naturality {U V} g := by
        ext x
        exact (kernelIso_pushout_hom_laws φ E).2.1 g x }
    (fun U r x ↦ (kernelIso_pushout_hom_laws φ E).2.2 U r x)

private theorem kernelIso_pushout_inv_laws (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (∀ U (x y : ((toCommModules X).obj 𝒢).val.obj U), kernelIso_pushout_invApp φ E U (x + y) = kernelIso_pushout_invApp φ E U x + kernelIso_pushout_invApp φ E U y) ∧
    (∀ {U V} (g : U ⟶ V) (x : ((toCommModules X).obj 𝒢).val.obj U),
      kernelIso_pushout_invApp φ E V (((toCommModules X).obj 𝒢).val.map g x) = ((isSquareZero_pushout_toOX φ E).targetModule (pushout_quotient_isIso φ E)).val.map g (kernelIso_pushout_invApp φ E U x)) ∧
    (∀ U (r : (commStructureSheaf X).obj.obj U) (x : ((toCommModules X).obj 𝒢).val.obj U),
      kernelIso_pushout_invApp φ E U (r • x) = r • kernelIso_pushout_invApp φ E U x) := by
  sorry

private def kernelIso_pushout_inv (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) : ((toCommModules X).obj 𝒢) ⟶ ((isSquareZero_pushout_toOX φ E).targetModule (pushout_quotient_isIso φ E)) where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom <| AddMonoidHom.mk' (kernelIso_pushout_invApp φ E U)
        ((kernelIso_pushout_inv_laws φ E).1 U)
      naturality {U V} g := by
        ext x
        exact (kernelIso_pushout_inv_laws φ E).2.1 g x }
    (fun U r x ↦ (kernelIso_pushout_inv_laws φ E).2.2 U r x)

private theorem kernelIso_pushout_inverse_laws (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    kernelIso_pushout_hom φ E ≫ kernelIso_pushout_inv φ E = 𝟙 _ ∧
    kernelIso_pushout_inv φ E ≫ kernelIso_pushout_hom φ E = 𝟙 _ := by
  sorry

/-- The kernel of the coefficient pushout is identified with the target coefficient module. -/
def kernelIso_pushout (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) : ((isSquareZero_pushout_toOX φ E).targetModule (pushout_quotient_isIso φ E)) ≅ ((toCommModules X).obj 𝒢) where
  hom := kernelIso_pushout_hom φ E
  inv := kernelIso_pushout_inv φ E
  hom_inv_id := (kernelIso_pushout_inverse_laws φ E).1
  inv_hom_id := (kernelIso_pushout_inverse_laws φ E).2

/-- The forward kernel identification is `kernelIso_pushout_homApp` on sections. -/
theorem kernelIso_pushout_hom_app (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ)
    (x : ((isSquareZero_pushout_toOX φ E).targetModule
        (pushout_quotient_isIso φ E)).val.obj U) :
    (kernelIso_pushout φ E).hom.val.app U x = kernelIso_pushout_homApp φ E U x :=
  rfl

/-- The inverse kernel identification is `kernelIso_pushout_invApp` on sections. -/
theorem kernelIso_pushout_inv_app (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ)
    (U : (smallEtaleSite X)ᵒᵖ) (n : ((toCommModules X).obj 𝒢).val.obj U) :
    (kernelIso_pushout φ E).inv.val.app U n = kernelIso_pushout_invApp φ E U n :=
  rfl

/-- Pushout of `0 ⟶ ℱ ⟶ 𝒪' ⟶ 𝒪_X ⟶ 0` along φ, as a square-zero f⁻¹𝒪_B-algebra
extension of 𝒪_X by 𝒢. -/
def pushout (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    SquareZeroAlgebraExtension f 𝒢 where
  middle := pushoutSheaf φ E
  proj := pushout_toOX φ E
  structureMap := pushout_fromOB φ E
  proj_locallySurjective := isLocallySurjective_pushout_toOX φ E
  proj_squareZero := isSquareZero_pushout_toOX φ E
  proj_quotient_isIso := pushout_quotient_isIso φ E
  commutes := by
    let p := fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢)
    let i := inl.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj 𝒢)
    let a := commInverseImageStructureSheafMap f
    have hi : i ≫ p = 𝟙 _ :=
      SheafOfModules.RingedSite.TrivSqZeroExt.fst_comp_inl.{u + 1, u, u}
        (commStructureSheaf X) ((toCommModules X).obj 𝒢)
    have hc : (a ≫ i) ≫ p = E.structureMap ≫ E.proj :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun h ↦ a ≫ h) hi).trans
          ((Category.comp_id _).trans E.commutes.symm))
    let l : commInverseImageStructureSheaf f ⟶ pushoutProduct φ E :=
      Limits.pullback.lift (a ≫ i) E.structureMap hc
    have hl : l ≫ pushoutProduct_fst φ E = a ≫ i :=
      Limits.pullback.lift_fst _ _ _
    change (l ≫ IdealSheaf.Quotient.projection (pushoutAntidiagonal φ E)) ≫
      IdealSheaf.Quotient.lift (pushoutAntidiagonal φ E)
        (pushoutProduct_toOX φ E) (pushoutAntidiagonal_le_ker φ E) = a
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun h ↦ l ≫ h)
        (IdealSheaf.Quotient.projection_comp_lift (pushoutAntidiagonal φ E)
          (pushoutProduct_toOX φ E) (pushoutAntidiagonal_le_ker φ E))).trans
        ((Category.assoc l (pushoutProduct_fst φ E) p).symm.trans
          ((congrArg (fun h ↦ h ≫ p) hl).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun h ↦ a ≫ h) hi).trans (Category.comp_id _))))))
  kernelIso := kernelIso_pushout φ E

/-- The carrier of `pushout φ E` is the antidiagonal quotient of the fibre product. -/
theorem pushout_middle (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (pushout φ E).middle = pushoutSheaf φ E :=
  rfl

/-- The projection of `pushout φ E` is the quotient lift of the fibre-product map to 𝒪_X. -/
theorem pushout_proj (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (pushout φ E).proj = pushout_toOX φ E :=
  rfl

/-- The structure map of `pushout φ E` is the composite of the fibre-product lift from
f⁻¹𝒪_B with the quotient projection. -/
theorem pushout_structureMap (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (pushout φ E).structureMap = pushout_fromOB φ E :=
  rfl

/-- The kernel identification of `pushout φ E` is `kernelIso_pushout`. -/
theorem pushout_kernelIso (φ : ℱ ⟶ 𝒢) (E : SquareZeroAlgebraExtension f ℱ) :
    (pushout φ E).kernelIso = kernelIso_pushout φ E :=
  rfl

/-- The ring-sheaf map of fibre products induced by a morphism of extensions. -/
private def pushoutProduct_map (φ : ℱ ⟶ 𝒢) {E₁ E₂ : SquareZeroAlgebraExtension f ℱ} (α : Hom E₁ E₂) :
    pushoutProduct φ E₁ ⟶ pushoutProduct φ E₂ :=
  Limits.pullback.lift (pushoutProduct_fst φ E₁)
    (pushoutProduct_snd φ E₁ ≫ α.hom) (by
      rw [Category.assoc, α.comm_proj]
      exact Limits.pullback.condition)

private theorem pushout_map_annihilates (φ : ℱ ⟶ 𝒢)
    {E₁ E₂ : SquareZeroAlgebraExtension f ℱ} (α : Hom E₁ E₂) :
    pushoutAntidiagonal φ E₁ ≤ KernelIdeal.subobject
      (pushoutProduct_map φ α ≫ IdealSheaf.Quotient.projection.{u + 1, u, u} (pushoutAntidiagonal φ E₂)) := by
  sorry

/-- The ring-sheaf map of algebra pushouts induced by a morphism of extensions. -/
private def pushout_map (φ : ℱ ⟶ 𝒢) {E₁ E₂ : SquareZeroAlgebraExtension f ℱ} (α : Hom E₁ E₂) :
    pushoutSheaf φ E₁ ⟶ pushoutSheaf φ E₂ :=
  IdealSheaf.Quotient.lift.{u + 1, u, u} (pushoutAntidiagonal φ E₁)
    (pushoutProduct_map φ α ≫ IdealSheaf.Quotient.projection.{u + 1, u, u} (pushoutAntidiagonal φ E₂))
    (pushout_map_annihilates φ α)

private theorem pushoutHom_laws (φ : ℱ ⟶ 𝒢)
    {E₁ E₂ : SquareZeroAlgebraExtension f ℱ} (α : Hom E₁ E₂) :
    (pushout_map φ α ≫ (pushout φ E₂).proj = (pushout φ E₁).proj) ∧
    ((pushout φ E₁).structureMap ≫ pushout_map φ α = (pushout φ E₂).structureMap) ∧
    (∀ (h : pushout_map φ α ≫ (pushout φ E₂).proj = (pushout φ E₁).proj),
      kernelHom (pushout_map φ α) h ≫ (pushout φ E₂).kernelIso.hom =
        (pushout φ E₁).kernelIso.hom) := by
  sorry

/-- The morphism `pushout φ E₁ ⟶ pushout φ E₂` induced by a morphism of extensions. -/
def pushoutHom (φ : ℱ ⟶ 𝒢) {E₁ E₂ : SquareZeroAlgebraExtension f ℱ} (α : Hom E₁ E₂) :
    Hom (pushout φ E₁) (pushout φ E₂) :=
  Hom.of (pushout_map φ α) (pushoutHom_laws φ α).1
    (pushoutHom_laws φ α).2.1 ((pushoutHom_laws φ α).2.2 _)

private theorem pushoutFunctor_laws (f : X ⟶ B) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    (∀ E : SquareZeroAlgebraExtension f ℱ, pushoutHom φ (Hom.id E) = Hom.id (pushout φ E)) ∧
    (∀ {E₁ E₂ E₃ : SquareZeroAlgebraExtension f ℱ} (α : Hom E₁ E₂) (β : Hom E₂ E₃),
      pushoutHom φ (Hom.comp α β) = Hom.comp (pushoutHom φ α) (pushoutHom φ β)) := by
  sorry

/-- The coefficient-pushout functor, sending an identity-base square-zero f⁻¹𝒪_B-algebra extension
of 𝒪_X by ℱ to the pushout along φ : ℱ ⟶ 𝒢. -/
def pushoutFunctor (f : X ⟶ B) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    SquareZeroAlgebraExtension f ℱ ⥤ SquareZeroAlgebraExtension f 𝒢 where
  obj := pushout φ
  map α := pushoutHom φ α
  map_id := (pushoutFunctor_laws f φ).1
  map_comp := (pushoutFunctor_laws f φ).2

/-- On objects, `pushoutFunctor f φ` is `pushout φ`. -/
theorem pushoutFunctor_obj (f : X ⟶ B) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢)
    (E : SquareZeroAlgebraExtension f ℱ) :
    (pushoutFunctor f φ).obj E = pushout φ E :=
  rfl

/-- On morphisms, `pushoutFunctor f φ` is `pushoutHom φ`. -/
theorem pushoutFunctor_map (f : X ⟶ B) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢)
    {E₁ E₂ : SquareZeroAlgebraExtension f ℱ} (α : Hom E₁ E₂) :
    (pushoutFunctor f φ).map α = pushoutHom φ α :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Hom.SquareZeroAlgebraExtension
