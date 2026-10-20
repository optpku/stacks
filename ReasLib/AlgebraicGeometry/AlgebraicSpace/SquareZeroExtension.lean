module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sheafification.CommRing
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.Quotient
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension.Module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TrivSqZeroExt
public import Mathlib.CategoryTheory.Category.Cat

/-! # Square-zero algebra extensions of the structure sheaf -/

@[expose] public section

-- Transparent constructions refer to private section functions and their proof laws.
-- This export-elaboration option preserves those implementation details as private.
set_option backward.privateInPublic true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.TrivSqZeroExt (trivSqZeroExt fst inl snd inr)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

namespace SquareZeroAlgebraExtension

/-- A square-zero algebra extension with a specified linear identification of its kernel. -/
structure Obj {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (ℱ : X.Modules) where
  /-- The unknown middle ring sheaf 𝒪'. -/
  middle : Sheaf (smallEtaleTopology X) CommRingCat.{u}
  /-- The square-zero locally surjective projection 𝒪' ⟶ 𝒪_X. -/
  proj : middle ⟶ commStructureSheaf X
  /-- The structure map f^♯ : f⁻¹𝒪_B ⟶ 𝒪'. -/
  structureMap : commInverseImageStructureSheaf f ⟶ middle
  /-- The projection 𝒪' ⟶ 𝒪_X is locally surjective. -/
  proj_locallySurjective : Sheaf.IsLocallySurjective proj
  /-- The kernel ideal of the projection 𝒪' ⟶ 𝒪_X is square zero. -/
  proj_squareZero : KernelIdeal.IsSquareZero proj
  /-- The first isomorphism theorem for the locally surjective projection 𝒪' ⟶ 𝒪_X. -/
  proj_quotient_isIso : IsIso (KernelIdeal.quotientComparison proj)
  /-- The structure map is a map of f⁻¹𝒪_B-algebras over 𝒪_X. -/
  commutes : structureMap ≫ proj = commInverseImageStructureSheafMap f
  /-- Identification of Ker(proj) with ℱ as 𝒪_X-modules. -/
  kernelIso :
    proj_squareZero.targetModule proj_quotient_isIso ≅ (toCommModules X).obj ℱ

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} {f : X ⟶ B} {ℱ : X.Modules}

/-- Assemble an identity-base square-zero f⁻¹𝒪_B-algebra extension from a middle ring sheaf,
structure maps, and a kernel identification with ℱ. -/
def of (middle : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (proj : middle ⟶ commStructureSheaf X)
    (structureMap : commInverseImageStructureSheaf f ⟶ middle)
    (proj_locallySurjective : Sheaf.IsLocallySurjective proj)
    (proj_squareZero : KernelIdeal.IsSquareZero proj)
    (proj_quotient_isIso : IsIso (KernelIdeal.quotientComparison proj))
    (commutes : structureMap ≫ proj = commInverseImageStructureSheafMap f)
    (kernelIso :
      proj_squareZero.targetModule proj_quotient_isIso ≅ (toCommModules X).obj ℱ) :
    Obj f ℱ where
  middle := middle
  proj := proj
  structureMap := structureMap
  proj_locallySurjective := proj_locallySurjective
  proj_squareZero := proj_squareZero
  proj_quotient_isIso := proj_quotient_isIso
  commutes := commutes
  kernelIso := kernelIso

/-- An identity-base extension has locally surjective square-zero projection, structure map
equal to f^♯ after composing with the projection, and kernel identified with ℱ. -/
theorem spec (E : Obj f ℱ) :
    Sheaf.IsLocallySurjective E.proj ∧
      KernelIdeal.IsSquareZero E.proj ∧
        E.structureMap ≫ E.proj = commInverseImageStructureSheafMap f ∧
          E.kernelIso.hom ≫ E.kernelIso.inv = 𝟙 _ ∧
            E.kernelIso.inv ≫ E.kernelIso.hom = 𝟙 _ :=
  ⟨E.proj_locallySurjective, E.proj_squareZero, E.commutes,
    E.kernelIso.hom_inv_id, E.kernelIso.inv_hom_id⟩

/-- The kernel section of 𝒪' corresponding to a coefficient of ℱ, via `kernelIso.inv`. -/
def kernelSection (E : Obj f ℱ) (U : (smallEtaleSite X)ᵒᵖ)
    (m : ((toCommModules X).obj ℱ).val.obj U) : E.middle.obj.obj U :=
  KernelIdeal.ιApp E.proj U
    ((E.proj_squareZero.targetModuleForgetIso E.proj_quotient_isIso).hom.hom.app U
      ((E.kernelIso.inv).val.app U m))

/-- The projection `𝒪_X ⊕ ℱ ⟶ 𝒪_X` is locally surjective. -/
instance instIsLocallySurjective_fst (ℱ : X.Modules) :
    Sheaf.IsLocallySurjective (fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ)) :=
  Presheaf.isLocallySurjective_of_surjective _ _ (fun U r ↦
    ⟨(inl (commStructureSheaf X) ((toCommModules X).obj ℱ)).hom.app U r, rfl⟩)

/-- The projection `𝒪_X ⊕ ℱ ⟶ 𝒪_X` is a square-zero extension. -/
theorem isSquareZero_fst (ℱ : X.Modules) :
    KernelIdeal.IsSquareZero (fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ)) :=
  sorry

/-- The inclusion `inr : ℱ ⟶ 𝒪_X ⊕ ℱ` lands in the kernel of `fst`. -/
private theorem inr_mem_sectionIdeal (ℱ : X.Modules) (U : (smallEtaleSite X)ᵒᵖ)
    (m : ((toCommModules X).obj ℱ).val.obj U) :
    inr.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ) m ∈
      KernelIdeal.sectionIdeal (fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ)) U :=
  sorry

/-- The split middle ring sheaf 𝒪_X ⊕ ℱ. -/
abbrev trivialMiddle (ℱ : X.Modules) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  trivSqZeroExt.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ)

/-- The split projection 𝒪_X ⊕ ℱ ⟶ 𝒪_X. -/
abbrev trivialProj (ℱ : X.Modules) :
    trivialMiddle ℱ ⟶ commStructureSheaf X :=
  fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ)

/-- The split structure map f^♯ followed by `inl`. -/
abbrev trivialStructureMap (f : X ⟶ B) (ℱ : X.Modules) :
    commInverseImageStructureSheaf f ⟶ trivialMiddle ℱ :=
  commInverseImageStructureSheafMap f ≫
    inl.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ)

private def kernelIso_fst_homApp (ℱ : X.Modules) (U : (smallEtaleSite X)ᵒᵖ)
    (x : ((isSquareZero_fst ℱ).targetModule (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).val.obj U) : ((toCommModules X).obj ℱ).val.obj U :=
  snd.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ)
                      (KernelIdeal.ιApp (trivialProj ℱ) U
                        (((isSquareZero_fst ℱ).targetModuleForgetIso
                            (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).hom.hom.app
                          U x))

private def kernelIso_fst_invApp (ℱ : X.Modules) (U : (smallEtaleSite X)ᵒᵖ)
    (n : ((toCommModules X).obj ℱ).val.obj U) : ((isSquareZero_fst ℱ).targetModule (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).val.obj U :=
  ((isSquareZero_fst ℱ).targetModuleForgetIso
                          (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).inv.hom.app
                      U ((KernelIdeal.sectionsIso (trivialProj ℱ) U).inv
                        ⟨inr.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ) n,
                          inr_mem_sectionIdeal ℱ U n⟩)

private theorem kernelIso_fst_hom_laws (ℱ : X.Modules) :
    (∀ U (x y : ((isSquareZero_fst ℱ).targetModule (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).val.obj U), kernelIso_fst_homApp ℱ U (x + y) = kernelIso_fst_homApp ℱ U x + kernelIso_fst_homApp ℱ U y) ∧
    (∀ {U V} (g : U ⟶ V) (x : ((isSquareZero_fst ℱ).targetModule (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).val.obj U),
      kernelIso_fst_homApp ℱ V (((isSquareZero_fst ℱ).targetModule (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).val.map g x) = ((toCommModules X).obj ℱ).val.map g (kernelIso_fst_homApp ℱ U x)) ∧
    (∀ U (r : (commStructureSheaf X).obj.obj U) (x : ((isSquareZero_fst ℱ).targetModule (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).val.obj U),
      kernelIso_fst_homApp ℱ U (r • x) = r • kernelIso_fst_homApp ℱ U x) := by
  sorry

private def kernelIso_fst_hom (ℱ : X.Modules) : ((isSquareZero_fst ℱ).targetModule (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))) ⟶ ((toCommModules X).obj ℱ) where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom <| AddMonoidHom.mk' (kernelIso_fst_homApp ℱ U)
        ((kernelIso_fst_hom_laws ℱ).1 U)
      naturality {U V} g := by
        ext x
        exact (kernelIso_fst_hom_laws ℱ).2.1 g x }
    (fun U r x ↦ (kernelIso_fst_hom_laws ℱ).2.2 U r x)

private theorem kernelIso_fst_inv_laws (ℱ : X.Modules) :
    (∀ U (x y : ((toCommModules X).obj ℱ).val.obj U), kernelIso_fst_invApp ℱ U (x + y) = kernelIso_fst_invApp ℱ U x + kernelIso_fst_invApp ℱ U y) ∧
    (∀ {U V} (g : U ⟶ V) (x : ((toCommModules X).obj ℱ).val.obj U),
      kernelIso_fst_invApp ℱ V (((toCommModules X).obj ℱ).val.map g x) = ((isSquareZero_fst ℱ).targetModule (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).val.map g (kernelIso_fst_invApp ℱ U x)) ∧
    (∀ U (r : (commStructureSheaf X).obj.obj U) (x : ((toCommModules X).obj ℱ).val.obj U),
      kernelIso_fst_invApp ℱ U (r • x) = r • kernelIso_fst_invApp ℱ U x) := by
  sorry

private def kernelIso_fst_inv (ℱ : X.Modules) : ((toCommModules X).obj ℱ) ⟶ ((isSquareZero_fst ℱ).targetModule (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))) where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom <| AddMonoidHom.mk' (kernelIso_fst_invApp ℱ U)
        ((kernelIso_fst_inv_laws ℱ).1 U)
      naturality {U V} g := by
        ext x
        exact (kernelIso_fst_inv_laws ℱ).2.1 g x }
    (fun U r x ↦ (kernelIso_fst_inv_laws ℱ).2.2 U r x)

private theorem kernelIso_fst_inverse_laws (ℱ : X.Modules) :
    kernelIso_fst_hom ℱ ≫ kernelIso_fst_inv ℱ = 𝟙 _ ∧
    kernelIso_fst_inv ℱ ≫ kernelIso_fst_hom ℱ = 𝟙 _ := by
  sorry

/-- The kernel of the split projection is linearly identified with its coefficient module. -/
def kernelIso_fst (ℱ : X.Modules) :
    (isSquareZero_fst ℱ).targetModule
      (KernelIdeal.quotientComparison_isIso (trivialProj ℱ)) ≅ (toCommModules X).obj ℱ where
  hom := kernelIso_fst_hom ℱ
  inv := kernelIso_fst_inv ℱ
  hom_inv_id := (kernelIso_fst_inverse_laws ℱ).1
  inv_hom_id := (kernelIso_fst_inverse_laws ℱ).2

/-- On a kernel section, `kernelIso_fst` is the second projection of `trivSqZeroExt`. -/
theorem kernelIso_fst_hom_apply (ℱ : X.Modules) (U : (smallEtaleSite X)ᵒᵖ)
    (x : ((isSquareZero_fst ℱ).targetModule
      (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).val.obj U) :
    (kernelIso_fst ℱ).hom.val.app U x =
      snd.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ)
        (KernelIdeal.ιApp (trivialProj ℱ) U
          (((isSquareZero_fst ℱ).targetModuleForgetIso
              (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).hom.hom.app U x)) :=
  rfl

/-- The inverse of `kernelIso_fst` is inclusion of ℱ by `inr`. -/
theorem kernelIso_fst_inv_apply (ℱ : X.Modules) (U : (smallEtaleSite X)ᵒᵖ)
    (n : ((toCommModules X).obj ℱ).val.obj U) :
    (kernelIso_fst ℱ).inv.val.app U n =
      ((isSquareZero_fst ℱ).targetModuleForgetIso
            (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).inv.hom.app
        U ((KernelIdeal.sectionsIso (trivialProj ℱ) U).inv
          ⟨inr.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ) n,
            inr_mem_sectionIdeal ℱ U n⟩) :=
  rfl

/-- The split extension 𝒪_X ⊕ ℱ of f⁻¹𝒪_B-algebras. -/
def trivial (f : X ⟶ B) (ℱ : X.Modules) : Obj f ℱ where
  middle := trivialMiddle ℱ
  proj := trivialProj ℱ
  structureMap := trivialStructureMap f ℱ
  proj_locallySurjective := instIsLocallySurjective_fst ℱ
  proj_squareZero := isSquareZero_fst ℱ
  proj_quotient_isIso := KernelIdeal.quotientComparison_isIso (trivialProj ℱ)
  commutes := by
    simp only [trivialStructureMap, trivialProj, Category.assoc,
      SheafOfModules.RingedSite.TrivSqZeroExt.fst_comp_inl, Category.comp_id]
  kernelIso := kernelIso_fst ℱ

/-- The carrier of the split extension is `trivSqZeroExt 𝒪_X ℱ`. -/
theorem trivial_middle (f : X ⟶ B) (ℱ : X.Modules) :
    (trivial f ℱ).middle =
      trivSqZeroExt.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ) :=
  rfl

/-- The projection of the split extension is `fst`. -/
theorem trivial_proj (f : X ⟶ B) (ℱ : X.Modules) :
    (trivial f ℱ).proj = fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ) :=
  rfl

/-- The structure map of the split extension is `inl` after f^♯. -/
theorem trivial_structureMap (f : X ⟶ B) (ℱ : X.Modules) :
    (trivial f ℱ).structureMap =
      commInverseImageStructureSheafMap f ≫
        inl.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ) :=
  rfl

/-- The kernel identification of the split extension is `kernelIso_fst`. -/
theorem trivial_kernelIso (f : X ⟶ B) (ℱ : X.Modules) :
    (trivial f ℱ).kernelIso = kernelIso_fst ℱ :=
  rfl

private theorem kernelHomApp_mem {E₁ E₂ : Obj f ℱ}
    (hom : E₁.middle ⟶ E₂.middle) (hcomm : hom ≫ E₂.proj = E₁.proj)
    (U : (smallEtaleSite X)ᵒᵖ)
    (x : (E₁.proj_squareZero.targetModule E₁.proj_quotient_isIso).val.obj U) :
    hom.hom.app U
      (KernelIdeal.ιApp E₁.proj U
        ((E₁.proj_squareZero.targetModuleForgetIso E₁.proj_quotient_isIso).hom.hom.app U x)) ∈
      KernelIdeal.sectionIdeal E₂.proj U := by
  sorry

/-- The 𝒪_X-module map on kernels induced by a ring-sheaf map over 𝒪_X. -/
private def kernelHomApp {E₁ E₂ : Obj f ℱ}
    (hom : E₁.middle ⟶ E₂.middle) (hcomm : hom ≫ E₂.proj = E₁.proj)
    (U : (smallEtaleSite X)ᵒᵖ)
    (x : (E₁.proj_squareZero.targetModule E₁.proj_quotient_isIso).val.obj U) :
    (E₂.proj_squareZero.targetModule E₂.proj_quotient_isIso).val.obj U :=
  (E₂.proj_squareZero.targetModuleForgetIso E₂.proj_quotient_isIso).inv.hom.app U
    ((KernelIdeal.sectionsIso E₂.proj U).inv
      ⟨hom.hom.app U
          (KernelIdeal.ιApp E₁.proj U
            ((E₁.proj_squareZero.targetModuleForgetIso E₁.proj_quotient_isIso).hom.hom.app U x)),
        kernelHomApp_mem hom hcomm U x⟩)

private theorem kernelHom_laws {E₁ E₂ : Obj f ℱ}
    (hom : E₁.middle ⟶ E₂.middle) (hcomm : hom ≫ E₂.proj = E₁.proj) :
    (∀ U (x y : (E₁.proj_squareZero.targetModule E₁.proj_quotient_isIso).val.obj U), kernelHomApp hom hcomm U (x + y) = kernelHomApp hom hcomm U x + kernelHomApp hom hcomm U y) ∧
    (∀ {U V} (g : U ⟶ V) (x : (E₁.proj_squareZero.targetModule E₁.proj_quotient_isIso).val.obj U),
      kernelHomApp hom hcomm V ((E₁.proj_squareZero.targetModule E₁.proj_quotient_isIso).val.map g x) = (E₂.proj_squareZero.targetModule E₂.proj_quotient_isIso).val.map g (kernelHomApp hom hcomm U x)) ∧
    (∀ U (r : (commStructureSheaf X).obj.obj U) (x : (E₁.proj_squareZero.targetModule E₁.proj_quotient_isIso).val.obj U),
      kernelHomApp hom hcomm U (r • x) = r • kernelHomApp hom hcomm U x) := by
  sorry

/-- The induced linear morphism between the kernels of a map over the structure sheaf. -/
def kernelHom {E₁ E₂ : Obj f ℱ}
    (hom : E₁.middle ⟶ E₂.middle) (hcomm : hom ≫ E₂.proj = E₁.proj) : (E₁.proj_squareZero.targetModule E₁.proj_quotient_isIso) ⟶ (E₂.proj_squareZero.targetModule E₂.proj_quotient_isIso) where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom <| AddMonoidHom.mk' (kernelHomApp hom hcomm U)
        ((kernelHom_laws hom hcomm).1 U)
      naturality {U V} g := by
        ext x
        exact (kernelHom_laws hom hcomm).2.1 g x }
    (fun U r x ↦ (kernelHom_laws hom hcomm).2.2 U r x)

/-- On sections, `kernelHom` is `kernelHomApp`. -/
theorem kernelHom_apply {E₁ E₂ : Obj f ℱ}
    (hom : E₁.middle ⟶ E₂.middle) (hcomm : hom ≫ E₂.proj = E₁.proj)
    (U : (smallEtaleSite X)ᵒᵖ)
    (x : (E₁.proj_squareZero.targetModule E₁.proj_quotient_isIso).val.obj U) :
    (kernelHom hom hcomm).val.app U x = kernelHomApp hom hcomm U x :=
  rfl

/-- Morphisms of identity-base square-zero f⁻¹𝒪_B-algebra extensions with the same
coefficient ℱ: a map of middle ring sheaves compatible with projections, structure maps,
and the identity on ℱ. -/
def Hom (E₁ E₂ : Obj f ℱ) :=
  { h : E₁.middle ⟶ E₂.middle //
    (h ≫ E₂.proj = E₁.proj) ∧
    (E₁.structureMap ≫ h = E₂.structureMap) ∧
    (∀ hp : h ≫ E₂.proj = E₁.proj,
      kernelHom h hp ≫ E₂.kernelIso.hom = E₁.kernelIso.hom) }

private theorem kernelHom_id (E : Obj f ℱ) :
    kernelHom (𝟙 E.middle) (Category.id_comp E.proj) = 𝟙 _ := by
  sorry

private theorem kernelHom_comp {E₁ E₂ E₃ : Obj f ℱ}
    (a : E₁.middle ⟶ E₂.middle) (b : E₂.middle ⟶ E₃.middle)
    (ha : a ≫ E₂.proj = E₁.proj) (hb : b ≫ E₃.proj = E₂.proj) :
    kernelHom (a ≫ b) (by rw [Category.assoc, hb, ha]) =
      kernelHom a ha ≫ kernelHom b hb := by
  sorry

namespace Hom

/-- The underlying morphism of middle ring sheaves of a morphism of extensions. -/
def hom {E₁ E₂ : Obj f ℱ} (α : Hom E₁ E₂) : E₁.middle ⟶ E₂.middle :=
  α.val

/-- A morphism of extensions commutes with the projections onto the structure sheaf. -/
theorem comm_proj {E₁ E₂ : Obj f ℱ} (α : Hom E₁ E₂) :
    α.hom ≫ E₂.proj = E₁.proj :=
  α.property.1

/-- A morphism of extensions commutes with the structure maps from f⁻¹𝒪_B. -/
theorem comm_structure {E₁ E₂ : Obj f ℱ} (α : Hom E₁ E₂) :
    E₁.structureMap ≫ α.hom = E₂.structureMap :=
  α.property.2.1

/-- A morphism of extensions induces the identity on the identified coefficient module. -/
theorem induces_id {E₁ E₂ : Obj f ℱ} (α : Hom E₁ E₂) :
    kernelHom α.hom α.comm_proj ≫ E₂.kernelIso.hom = E₁.kernelIso.hom :=
  α.property.2.2 α.comm_proj

/-- Morphisms of extensions are determined by their underlying ring-sheaf morphisms. -/
theorem ext {E₁ E₂ : Obj f ℱ} {α β : Hom E₁ E₂} (h : α.hom = β.hom) : α = β :=
  Subtype.ext h

/-- Assemble a morphism of extensions from a ring-sheaf map and the three compatibility
conditions. -/
def of {E₁ E₂ : Obj f ℱ} (hom : E₁.middle ⟶ E₂.middle)
    (comm_proj : hom ≫ E₂.proj = E₁.proj)
    (comm_structure : E₁.structureMap ≫ hom = E₂.structureMap)
    (induces_id :
      kernelHom hom comm_proj ≫ E₂.kernelIso.hom = E₁.kernelIso.hom) :
    Hom E₁ E₂ :=
  ⟨hom, comm_proj, comm_structure, fun _ ↦ induces_id⟩

/-- A morphism of extensions commutes with projections and structure maps and induces the
identity on ℱ. -/
theorem spec {E₁ E₂ : Obj f ℱ} (α : Hom E₁ E₂) :
    α.hom ≫ E₂.proj = E₁.proj ∧
      E₁.structureMap ≫ α.hom = E₂.structureMap ∧
        kernelHom α.hom α.comm_proj ≫ E₂.kernelIso.hom = E₁.kernelIso.hom :=
  ⟨α.comm_proj, α.comm_structure, α.induces_id⟩

/-- Identity morphisms of identity-base square-zero extensions. -/
def id (E : Obj f ℱ) : Hom E E :=
  of (𝟙 E.middle) (Category.id_comp _) (Category.comp_id _)
    (by rw [kernelHom_id, Category.id_comp])

/-- Composition of morphisms of identity-base square-zero extensions. -/
def comp {E₁ E₂ E₃ : Obj f ℱ} (α : Hom E₁ E₂) (β : Hom E₂ E₃) :
    Hom E₁ E₃ :=
  of (α.hom ≫ β.hom)
    (by rw [Category.assoc, β.comm_proj, α.comm_proj])
    (by rw [← Category.assoc, α.comm_structure, β.comm_structure])
    (by rw [kernelHom_comp α.hom β.hom α.comm_proj β.comm_proj,
      Category.assoc, β.induces_id, α.induces_id])

end Hom

/-- Identity morphisms of identity-base square-zero extensions. -/
abbrev idHom (E : Obj f ℱ) : Hom E E :=
  Hom.id E

/-- The category of square-zero algebra extensions with fixed coefficient module. -/
def category (f : X ⟶ B) (ℱ : X.Modules) : Cat.{u + 1, u + 1} :=
  ⟨Obj f ℱ, {
    Hom := Hom
    id := Hom.id
    comp := Hom.comp
    id_comp := fun α ↦ by
      apply Hom.ext
      exact Category.id_comp α.hom
    comp_id := fun α ↦ by
      apply Hom.ext
      exact Category.comp_id α.hom
    assoc := fun α β γ ↦ by
      apply Hom.ext
      exact Category.assoc _ _ _
  }⟩

end SquareZeroAlgebraExtension

/-- The carrier of the category of square-zero algebra extensions with fixed coefficients. -/
abbrev SquareZeroAlgebraExtension {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (ℱ : X.Modules) := SquareZeroAlgebraExtension.category f ℱ

namespace SquareZeroAlgebraExtension

/-- The identity morphism of the category of extensions is `idHom`. -/
theorem idHom_eq {S : Scheme.{u}} {X B : AlgebraicSpace S}
    {f : X ⟶ B} {ℱ : X.Modules} (E : SquareZeroAlgebraExtension f ℱ) :
    𝟙 E = idHom E :=
  rfl

end SquareZeroAlgebraExtension

end AlgebraicGeometry.AlgebraicSpace.Hom
