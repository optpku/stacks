/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Algebra.Category.Ring.Limits
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.DifferentialGraded
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction.Complex
public import ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct.Unit

/-!
# Tensoring with a complex over a commutative algebra sheaf

This is the coefficient-linear owner of the sectionwise construction used by Lemma 22.35.1.
The coefficient ring `R` is kept explicit, while the cohomological grading remains `ℤ`.
The older integral ringed-site API is intentionally independent of this file.
-/

@[expose] public section

noncomputable section

universe r u v w z t

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open SheafOfModules.RingedSite.ModuleSheafification
open scoped SheafOfModules.CommAlg

namespace SheafOfModules.CommAlg.TensorWithObject

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J (CommAlgCat.{w} R)}

/-- Right DG modules over the endomorphism DGA. -/
@[stacks 09LV "right DG modules over the endomorphism DGA"]
abbrev Modules (K : Complex.{r, u, v, w, max u z} O) :=
  DifferentialGradedModule.{r, max u z, max u z} (endDGA K)

/-- Degree-`n` sections of `K`, restricted along the base-ring map to an `R`-module. -/
@[stacks 09LV "degreewise sections as restricted scalar modules"]
abbrev Section (K : Complex.{r, u, v, w, max u z} O) (U : Cᵒᵖ) (n : ℤ) :
    ModuleCat.{max u z} R :=
  (ModuleCat.restrictScalars (SheafOfModules.CommAlg.baseRingHom O U)).obj
    ((K.X n).val.obj U)

/-- Evaluation of a homogeneous endomorphism on sections. -/
@[stacks 09LV "evaluation of a homogeneous endomorphism on sections"]
def actionValue (K : Complex.{r, u, v, w, max u z} O) (U : Cᵒᵖ) (i p : ℤ)
    (a : (endDGA K).X i) (x : Section K U p) : Section K U (i + p) :=
  ((((a : Cochain K K i).v p (p + i) rfl) ≫
      eqToHom (congrArg K.X (add_comm p i))).val.app U) x

/-- The homogeneous endomorphism action on sections as an `R`-bilinear map. -/
@[stacks 09LV "sectionwise endomorphism action"]
def action (K : Complex.{r, u, v, w, max u z} O) (U : Cᵒᵖ) (i p : ℤ) :
    (endDGA K).X i →ₗ[R] Section K U p →ₗ[R] Section K U (i + p) where
  toFun a :=
    { toFun := actionValue K U i p a
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- Sections of `K` with their left action by the endomorphism DGA. -/
@[stacks 09LV "sections as a left endomorphism module"]
def sectionModule (K : Complex.{r, u, v, w, max u z} O) (U : Cᵒᵖ) :
    LeftDifferentialGradedModule.{r, max u z, max u z} (endDGA K) where
  X := Section K U
  d n :=
    { toFun := fun x ↦ (K.d n (n + 1)).val.app U x
      map_add' := sorry
      map_smul' := sorry }
  smul := action K U
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- Restriction of sections is a morphism of left endomorphism modules. -/
@[stacks 09LV "restriction of endomorphism modules of sections"]
def restriction (K : Complex.{r, u, v, w, max u z} O) {U V : Cᵒᵖ} (f : U ⟶ V) :
    sectionModule K U ⟶ sectionModule K V where
  hom n :=
    { toFun := fun x ↦ (K.X n).val.map f x
      map_add' := sorry
      map_smul' := sorry }
  comm_d := sorry
  comm_smul := sorry

/-- Multiplication by a local structure-ring section on a homogeneous section module. -/
@[stacks 09LV "local scalar action on homogeneous sections"]
def scalarValue (K : Complex.{r, u, v, w, max u z} O) (U : Cᵒᵖ) (n : ℤ)
    (rU : (CategoryTheory.Sheaf.CommAlg.ring O).obj.obj U)
    (x : Section K U n) : Section K U n :=
  rU • (x : ((K.X n).val.obj U))

/-- Multiplication by a local section is an endomorphism of the left section module. -/
@[stacks 09LV "local scalar endomorphism of the section module"]
def scalarAction (K : Complex.{r, u, v, w, max u z} O) (U : Cᵒᵖ)
    (rU : (CategoryTheory.Sheaf.CommAlg.ring O).obj.obj U) :
    sectionModule K U ⟶ sectionModule K U where
  hom n :=
    { toFun := scalarValue K U n rU
      map_add' := sorry
      map_smul' := sorry }
  comm_d := sorry
  comm_smul := sorry

/-- The degree-`n` sectionwise relative tensor product before sheafification. -/
@[stacks 09LV "sectionwise relative tensor family"]
def Family (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    (U : Cᵒᵖ) (n : ℤ) :
    ModuleCat.{max u z} R :=
  DifferentialGradedModule.TensorProduct.family M (sectionModule K U) n

/-- The structure-ring action on one degree of the sectionwise relative tensor family. -/
@[stacks 09LV "structure-ring action on the relative tensor family"]
def familyAction (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    (U : Cᵒᵖ) (n : ℤ) :
    (CategoryTheory.Sheaf.CommAlg.ring O).obj.obj U →+* Module.End R (Family K M U n) where
  toFun rU :=
    { toFun := DifferentialGradedModule.TensorProduct.mapLeftLinear
        (R := R) (A := endDGA K) M (scalarAction K U rU) n
      map_add' := sorry
      map_smul' := sorry }
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The canonical local-ring module structure on the sectionwise relative tensor family. -/
@[stacks 09LV "module structure on the relative tensor family"]
noncomputable instance familyModule (K : Complex.{r, u, v, w, max u z} O)
    (M : Modules K) (U : Cᵒᵖ) (n : ℤ) :
    Module ((CategoryTheory.Sheaf.CommAlg.ring O).obj.obj U) (Family K M U n) :=
  Module.compHom _ (familyAction K M U n)

/-- Restriction on the section factor induces a semilinear map on each relative tensor family. -/
@[stacks 09LV "restriction on the sectionwise relative tensor family"]
def familyRestriction (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℤ) :
    Family K M U n →ₛₗ[((CategoryTheory.Sheaf.CommAlg.ring O).obj.map f).hom]
      Family K M V n where
  toFun := DifferentialGradedModule.TensorProduct.mapLeftLinear
    (R := R) (A := endDGA K) M (restriction K f) n
  map_add' := sorry
  map_smul' := sorry

/-- Restriction on a relative tensor family as a morphism after restricting scalars. -/
@[stacks 09LV "restriction morphism on the sectionwise relative tensor family"]
def familyRestrictionHom (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℤ) :
    ModuleCat.of ((CategoryTheory.Sheaf.CommAlg.ring O).obj.obj U) (Family K M U n) ⟶
      (ModuleCat.restrictScalars
        ((CategoryTheory.Sheaf.CommAlg.ring O).obj.map f).hom).obj
        (ModuleCat.of ((CategoryTheory.Sheaf.CommAlg.ring O).obj.obj V) (Family K M V n)) :=
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars
      ((CategoryTheory.Sheaf.CommAlg.ring O).obj.map f).hom).obj
      (ModuleCat.of ((CategoryTheory.Sheaf.CommAlg.ring O).obj.obj V) (Family K M V n)))
    { toFun := DifferentialGradedModule.TensorProduct.mapLeftLinear
        (R := R) (A := endDGA K) M (restriction K f) n
      map_add' := sorry
      map_smul' := sorry }

/-- Degree `n` of the relative tensor construction as a presheaf of local modules. -/
@[stacks 09LV "degreewise relative tensor presheaf"]
def term (K : Complex.{r, u, v, w, max u z} O) (M : Modules K) (n : ℤ) :
    PresheafOfModules.{max u z} (CategoryTheory.Sheaf.CommAlg.ring O).obj where
  obj U := ModuleCat.of ((CategoryTheory.Sheaf.CommAlg.ring O).obj.obj U)
    (Family K M U n)
  map f := familyRestrictionHom K M f n
  map_id := sorry
  map_comp := sorry

/-- The relative tensor differential as a morphism of module presheaves. -/
@[stacks 09LV "relative tensor differential"]
def differential (K : Complex.{r, u, v, w, max u z} O) (M : Modules K) (n : ℤ) :
    term K M n ⟶ term K M (n + 1) where
  app U := ModuleCat.ofHom
    { toFun := DifferentialGradedModule.TensorProduct.differential M (sectionModule K U) n
      map_add' := sorry
      map_smul' := sorry }
  naturality := sorry

/-- Consecutive relative tensor differentials compose to zero. -/
@[stacks 09LV "square-zero law for the relative tensor differential"]
theorem differential_comp (K : Complex.{r, u, v, w, max u z} O)
    (M : Modules K) (n : ℤ) :
    differential K M n ≫ differential K M (n + 1) = 0 := sorry

/-- The sectionwise relative tensor product as a cochain complex of module presheaves. -/
@[stacks 09LV "relative tensor presheaf complex"]
def presheafComplex (K : Complex.{r, u, v, w, max u z} O) (M : Modules K) :
    CochainComplex (PresheafOfModules.{max u z} (CategoryTheory.Sheaf.CommAlg.ring O).obj) ℤ :=
  CochainComplex.of (term K M) (differential K M) (differential_comp K M)

/-- A homogeneous DG-module map induces a degree-shifting map of relative tensor terms. -/
@[stacks 09LV "homogeneous map on relative tensor terms"]
def termMap (K : Complex.{r, u, v, w, max u z} O) {M N : Modules K} {j : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M N j) (n : ℤ) :
    term K M n ⟶ term K N (n + j) where
  app U := ModuleCat.ofHom
    { toFun := DifferentialGradedModule.TensorProduct.mapLinear (sectionModule K U) g n
      map_add' := sorry
      map_smul' := sorry }
  naturality := sorry

/-- The homogeneous map of tensor terms assembled as a cochain of presheaves. -/
@[stacks 09LV "relative tensor presheaf map"]
def presheafMap (K : Complex.{r, u, v, w, max u z} O) {M N : Modules K} {j : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M N j) :
    Cochain (presheafComplex K M) (presheafComplex K N) j :=
  Cochain.mk fun p _q hpq ↦ termMap K g p ≫ eqToHom (congrArg (term K N) hpq)

section Sheafification

variable [HasWeakSheafify J AddCommGrpCat.{max u z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u z}]

/-- The sheafified sectionwise relative tensor product. -/
@[stacks 09LV "sheafified relative tensor complex"]
def obj (K : Complex.{r, u, v, w, max u z} O) (M : Modules K) :
    Complex.{r, u, v, w, max u z} O :=
  ((moduleSheafification (CategoryTheory.Sheaf.CommAlg.commRing O)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (presheafComplex K M)

/-- Sheafification of the homogeneous relative tensor map. -/
@[stacks 09LV "sheafified relative tensor map"]
def map (K : Complex.{r, u, v, w, max u z} O) {M N : Modules K} {j : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M N j) :
    Cochain (obj K M) (obj K N) j :=
  (presheafMap K g).map (moduleSheafification (CategoryTheory.Sheaf.CommAlg.commRing O))

/-- Lemma 22.35.1 (09LV): the sheafified relative tensor DG functor. -/
@[stacks 09LV "tensor with a complex over its endomorphism DGA"]
def tensorFunctor (K : Complex.{r, u, v, w, max u z} O) :
    DgFunctor R (Modules K) (Complex.{r, u, v, w, max u z} O) where
  obj := obj K
  map := map K
  map_add := sorry
  map_smul := sorry
  map_d := sorry
  map_id := sorry
  map_comp := sorry

/-- Tensoring with `K` sends a right DG module to its sheafified tensor complex. -/
@[simp, stacks 09LV "object formula for tensoring with a complex"]
theorem tensorFunctor_obj (K : Complex.{r, u, v, w, max u z} O) (M : Modules K) :
    (tensorFunctor K).obj M = obj K M := sorry

/-- The homogeneous map of tensoring with `K` is the sheafified tensor map. -/
@[simp, stacks 09LV "map formula for tensoring with a complex"]
theorem tensorFunctor_map (K : Complex.{r, u, v, w, max u z} O)
    {M N : Modules K} {j : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M N j) :
    (tensorFunctor K).map g = map K g := sorry

end Sheafification

/-- The tensor-unit isomorphism on one site object and one degree. -/
@[stacks 09LV "sectionwise tensor-unit isomorphism"]
def regularTermIso (K : Complex.{r, u, v, w, max u z} O) (U : Cᵒᵖ) (n : ℤ) :
    (term K (endDGA K).regularModule n).obj U ≅ (K.X n).val.obj U where
  hom := ModuleCat.ofHom
    { toFun := fun x ↦ ModuleCat.Hom.hom
        ((DifferentialGradedModule.TensorProduct.regularTensorIso
          (sectionModule K U)).hom.f n) x
      map_add' := sorry
      map_smul' := sorry }
  inv := ModuleCat.ofHom
    { toFun := fun x ↦ ModuleCat.Hom.hom
        ((DifferentialGradedModule.TensorProduct.regularTensorIso
          (sectionModule K U)).inv.f n) x
      map_add' := sorry
      map_smul' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The sectionwise tensor-unit isomorphism as an isomorphism of module presheaves. -/
@[stacks 09LV "presheaf tensor-unit isomorphism"]
def regularPresheafTermIso (K : Complex.{r, u, v, w, max u z} O) (n : ℤ) :
    term K (endDGA K).regularModule n ≅ (K.X n).val :=
  PresheafOfModules.isoMk (fun U ↦ regularTermIso K U n) sorry

/-- Before sheafification, tensoring the regular module recovers the underlying module presheaf. -/
@[stacks 09LV "presheaf-level tensor-unit comparison"]
def regularPresheafIso (K : Complex.{r, u, v, w, max u z} O) :
    presheafComplex K (endDGA K).regularModule ≅
      underlyingComplex (CategoryTheory.Sheaf.CommAlg.commRing O) K :=
  HomologicalComplex.Hom.isoOfComponents (regularPresheafTermIso K) sorry

section Sheafification

variable [HasWeakSheafify J AddCommGrpCat.{max u z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u z}]

/-- Sheafification of the underlying presheaf complex recovers `K`. -/
@[stacks 09LV "sheafification bridge for the tensor unit"]
def sheafifiedUnderlyingIso (K : Complex.{r, u, v, w, max u z} O) :
    ((moduleSheafification (CategoryTheory.Sheaf.CommAlg.commRing O)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (underlyingComplex (CategoryTheory.Sheaf.CommAlg.commRing O) K) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ SheafOfModules.RingedSite.moduleSheafificationValIso
      (CategoryTheory.Sheaf.CommAlg.commRing O) (K.X n)) sorry

/-- Lemma 22.35.1 (09LV): the regular endomorphism module maps to `K`. -/
@[stacks 09LV "the regular endomorphism module maps to the original complex"]
def objRegularIso (K : Complex.{r, u, v, w, max u z} O) :
    (tensorFunctor K).obj (endDGA K).regularModule ≅ K :=
  ((moduleSheafification (CategoryTheory.Sheaf.CommAlg.commRing O)).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso (regularPresheafIso K) ≪≫
    sheafifiedUnderlyingIso K

/-- Lemma 22.35.1 (09LV): tensoring with `K` preserves arbitrary direct sums. -/
@[stacks 09LV "tensor with a complex preserves arbitrary direct sums"]
instance preservesCoproducts (K : Complex.{r, u, v, w, max u z} O) (ι : Type t) :
    PreservesColimitsOfShape (Discrete ι) (tensorFunctor K).mapComp := sorry

end Sheafification

end SheafOfModules.CommAlg.TensorWithObject
