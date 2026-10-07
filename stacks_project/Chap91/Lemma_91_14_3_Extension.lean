module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.Quotient
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension.Module
public import stacks_project.Chap66.Lemma_66_28_1_Hom
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap75.Lemma_75_19_1_Instances
public import stacks_project.Chap91.«91_10_5_1_TrivSqZeroExt»

/-!
# Identity-base square-zero f⁻¹𝒪_B-algebra extensions of 𝒪_X

After identifying underlying topoi, a square-zero extension of 𝒪_X by an
𝒪_X-module ℱ as an f⁻¹𝒪_B-algebra is a middle ring sheaf 𝒪' on X_étale with
locally surjective square-zero projection onto 𝒪_X, structure map from
f⁻¹𝒪_B, and kernel identified with ℱ as an 𝒪_X-module. This is the identity-base
case of 91.13.0.1 (π = 𝟙, c = 0). Coefficients are not assumed quasi-coherent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.TrivSqZeroExt (trivSqZeroExt fst inl snd inr)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Commutative-ring-valued weak sheafification exists on the small étale site. -/
instance smallEtaleTopology_hasWeakSheafify_commRingCat :
    HasWeakSheafify (smallEtaleTopology X) CommRingCat.{u} :=
  sorry

/-- On the small étale topology, sheafification equivalences for commutative rings are the
locally bijective morphisms. -/
instance smallEtaleTopology_wEqualsLocallyBijective_commRingCat :
    (smallEtaleTopology X).WEqualsLocallyBijective CommRingCat.{u} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- An identity-base square-zero extension of 𝒪_X by ℱ as an f⁻¹𝒪_B-algebra: a middle
ring sheaf 𝒪' on X_étale, a locally surjective square-zero projection onto 𝒪_X whose
kernel is identified with ℱ as an 𝒪_X-module, and a structure map from f⁻¹𝒪_B. -/
structure SquareZeroAlgebraExtension {S : Scheme.{u}} {X B : AlgebraicSpace S}
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

namespace SquareZeroAlgebraExtension

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
    SquareZeroAlgebraExtension f ℱ where
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
theorem spec (E : SquareZeroAlgebraExtension f ℱ) :
    Sheaf.IsLocallySurjective E.proj ∧
      KernelIdeal.IsSquareZero E.proj ∧
        E.structureMap ≫ E.proj = commInverseImageStructureSheafMap f ∧
          E.kernelIso.hom ≫ E.kernelIso.inv = 𝟙 _ ∧
            E.kernelIso.inv ≫ E.kernelIso.hom = 𝟙 _ :=
  sorry

/-- The kernel section of 𝒪' corresponding to a coefficient of ℱ, via `kernelIso.inv`. -/
def kernelSection (E : SquareZeroAlgebraExtension f ℱ) (U : (smallEtaleSite X)ᵒᵖ)
    (m : ((toCommModules X).obj ℱ).val.obj U) : E.middle.obj.obj U :=
  KernelIdeal.ιApp E.proj U
    ((E.proj_squareZero.targetModuleForgetIso E.proj_quotient_isIso).hom.hom.app U
      ((E.kernelIso.inv).val.app U m))

/-- The projection `𝒪_X ⊕ ℱ ⟶ 𝒪_X` is locally surjective. -/
instance instIsLocallySurjective_fst (ℱ : X.Modules) :
    Sheaf.IsLocallySurjective (fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ)) :=
  sorry

/-- The projection `𝒪_X ⊕ ℱ ⟶ 𝒪_X` is a square-zero extension. -/
theorem isSquareZero_fst (ℱ : X.Modules) :
    KernelIdeal.IsSquareZero (fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ)) :=
  sorry

/-- The inclusion `inr : ℱ ⟶ 𝒪_X ⊕ ℱ` lands in the kernel of `fst`. -/
theorem inr_mem_sectionIdeal (ℱ : X.Modules) (U : (smallEtaleSite X)ᵒᵖ)
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

/-- 𝒪_X-linear identification of `Ker(𝒪_X ⊕ ℱ ⟶ 𝒪_X)` with ℱ, via `snd` and `inr`. -/
def kernelIso_fst (ℱ : X.Modules) :
    (isSquareZero_fst ℱ).targetModule
      (KernelIdeal.quotientComparison_isIso (trivialProj ℱ)) ≅ (toCommModules X).obj ℱ where
  hom :=
    { val :=
        PresheafOfModules.homMk
          { app U :=
              AddCommGrpCat.ofHom <|
                AddMonoidHom.mk'
                  (fun x ↦
                    snd.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ)
                      (KernelIdeal.ιApp (trivialProj ℱ) U
                        (((isSquareZero_fst ℱ).targetModuleForgetIso
                            (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).hom.hom.app
                          U x)))
                  sorry
            naturality {_ _} _ := sorry }
          (fun _ _ _ ↦ sorry) }
  inv :=
    { val :=
        PresheafOfModules.homMk
          { app U :=
              AddCommGrpCat.ofHom <|
                AddMonoidHom.mk'
                  (fun n ↦
                    ((isSquareZero_fst ℱ).targetModuleForgetIso
                          (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).inv.hom.app
                      U ((KernelIdeal.sectionsIso (trivialProj ℱ) U).inv
                        ⟨inr.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ) n,
                          inr_mem_sectionIdeal ℱ U n⟩))
                  sorry
            naturality {_ _} _ := sorry }
          (fun _ _ _ ↦ sorry) }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- On a kernel section, `kernelIso_fst` is the second projection of `trivSqZeroExt`. -/
theorem kernelIso_fst_hom_apply (ℱ : X.Modules) (U : (smallEtaleSite X)ᵒᵖ)
    (x : ((isSquareZero_fst ℱ).targetModule
      (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).val.obj U) :
    (kernelIso_fst ℱ).hom.val.app U x =
      snd.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ)
        (KernelIdeal.ιApp (trivialProj ℱ) U
          (((isSquareZero_fst ℱ).targetModuleForgetIso
              (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).hom.hom.app U x)) :=
  sorry

/-- The inverse of `kernelIso_fst` is inclusion of ℱ by `inr`. -/
theorem kernelIso_fst_inv_apply (ℱ : X.Modules) (U : (smallEtaleSite X)ᵒᵖ)
    (n : ((toCommModules X).obj ℱ).val.obj U) :
    (kernelIso_fst ℱ).inv.val.app U n =
      ((isSquareZero_fst ℱ).targetModuleForgetIso
            (KernelIdeal.quotientComparison_isIso (trivialProj ℱ))).inv.hom.app
        U ((KernelIdeal.sectionsIso (trivialProj ℱ) U).inv
          ⟨inr.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ) n,
            inr_mem_sectionIdeal ℱ U n⟩) :=
  sorry

/-- The split extension 𝒪_X ⊕ ℱ of f⁻¹𝒪_B-algebras. -/
def trivial (f : X ⟶ B) (ℱ : X.Modules) : SquareZeroAlgebraExtension f ℱ where
  middle := trivialMiddle ℱ
  proj := trivialProj ℱ
  structureMap := trivialStructureMap f ℱ
  proj_locallySurjective := instIsLocallySurjective_fst ℱ
  proj_squareZero := isSquareZero_fst ℱ
  proj_quotient_isIso := KernelIdeal.quotientComparison_isIso (trivialProj ℱ)
  commutes := sorry
  kernelIso := kernelIso_fst ℱ

/-- The coefficient projection of the split extension, as `snd`. -/
def trivialKernelOut (ℱ : X.Modules) (U : (smallEtaleSite X)ᵒᵖ)
    (x : (trivialMiddle ℱ).obj.obj U) :
    ((toCommModules X).obj ℱ).val.obj U :=
  snd.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ) x

/-- The carrier of the split extension is `trivSqZeroExt 𝒪_X ℱ`. -/
theorem trivial_middle (f : X ⟶ B) (ℱ : X.Modules) :
    (trivial f ℱ).middle =
      trivSqZeroExt.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ) :=
  sorry

/-- The projection of the split extension is `fst`. -/
theorem trivial_proj (f : X ⟶ B) (ℱ : X.Modules) :
    (trivial f ℱ).proj = fst.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ) :=
  sorry

/-- The structure map of the split extension is `inl` after f^♯. -/
theorem trivial_structureMap (f : X ⟶ B) (ℱ : X.Modules) :
    (trivial f ℱ).structureMap =
      commInverseImageStructureSheafMap f ≫
        inl.{u + 1, u, u} (commStructureSheaf X) ((toCommModules X).obj ℱ) :=
  sorry

/-- The kernel identification of the split extension is `kernelIso_fst`. -/
theorem trivial_kernelIso (f : X ⟶ B) (ℱ : X.Modules) :
    (trivial f ℱ).kernelIso = kernelIso_fst ℱ :=
  sorry

/-- The 𝒪_X-module map on kernels induced by a ring-sheaf map over 𝒪_X. -/
def kernelHomApp {E₁ E₂ : SquareZeroAlgebraExtension f ℱ}
    (hom : E₁.middle ⟶ E₂.middle) (hcomm : hom ≫ E₂.proj = E₁.proj)
    (U : (smallEtaleSite X)ᵒᵖ)
    (x : (E₁.proj_squareZero.targetModule E₁.proj_quotient_isIso).val.obj U) :
    (E₂.proj_squareZero.targetModule E₂.proj_quotient_isIso).val.obj U :=
  (E₂.proj_squareZero.targetModuleForgetIso E₂.proj_quotient_isIso).inv.hom.app U
    ((KernelIdeal.sectionsIso E₂.proj U).inv
      ⟨hom.hom.app U
          (KernelIdeal.ιApp E₁.proj U
            ((E₁.proj_squareZero.targetModuleForgetIso E₁.proj_quotient_isIso).hom.hom.app U x)),
        sorry⟩)

/-- The 𝒪_X-module morphism Ker(proj₁) ⟶ Ker(proj₂) induced by a map of middle ring sheaves. -/
def kernelHom {E₁ E₂ : SquareZeroAlgebraExtension f ℱ}
    (hom : E₁.middle ⟶ E₂.middle) (hcomm : hom ≫ E₂.proj = E₁.proj) :
    E₁.proj_squareZero.targetModule E₁.proj_quotient_isIso ⟶
      E₂.proj_squareZero.targetModule E₂.proj_quotient_isIso where
  val :=
    PresheafOfModules.homMk
      { app U :=
          AddCommGrpCat.ofHom <|
            AddMonoidHom.mk' (fun x ↦ kernelHomApp hom hcomm U x) sorry
        naturality {_ _} _ := sorry }
      (fun _ _ _ ↦ sorry)

/-- On sections, `kernelHom` is `kernelHomApp`. -/
theorem kernelHom_apply {E₁ E₂ : SquareZeroAlgebraExtension f ℱ}
    (hom : E₁.middle ⟶ E₂.middle) (hcomm : hom ≫ E₂.proj = E₁.proj)
    (U : (smallEtaleSite X)ᵒᵖ)
    (x : (E₁.proj_squareZero.targetModule E₁.proj_quotient_isIso).val.obj U) :
    (kernelHom hom hcomm).val.app U x = kernelHomApp hom hcomm U x :=
  sorry

/-- Morphisms of identity-base square-zero f⁻¹𝒪_B-algebra extensions with the same
coefficient ℱ: a map of middle ring sheaves compatible with projections, structure maps,
and the identity on ℱ. -/
structure Hom (E₁ E₂ : SquareZeroAlgebraExtension f ℱ) where
  /-- The underlying morphism of middle ring sheaves 𝒪'₁ ⟶ 𝒪'₂. -/
  hom : E₁.middle ⟶ E₂.middle
  /-- Compatibility with the projections onto 𝒪_X. -/
  comm_proj : hom ≫ E₂.proj = E₁.proj
  /-- Compatibility with the structure maps from f⁻¹𝒪_B. -/
  comm_structure : E₁.structureMap ≫ hom = E₂.structureMap
  /-- The morphism induces the identity on ℱ after transporting along `kernelIso`. -/
  induces_id :
    kernelHom hom comm_proj ≫ E₂.kernelIso.hom = E₁.kernelIso.hom

namespace Hom

/-- Assemble a morphism of extensions from a ring-sheaf map and the three compatibility
conditions. -/
def of {E₁ E₂ : SquareZeroAlgebraExtension f ℱ} (hom : E₁.middle ⟶ E₂.middle)
    (comm_proj : hom ≫ E₂.proj = E₁.proj)
    (comm_structure : E₁.structureMap ≫ hom = E₂.structureMap)
    (induces_id :
      kernelHom hom comm_proj ≫ E₂.kernelIso.hom = E₁.kernelIso.hom) :
    Hom E₁ E₂ where
  hom := hom
  comm_proj := comm_proj
  comm_structure := comm_structure
  induces_id := induces_id

/-- A morphism of extensions commutes with projections and structure maps and induces the
identity on ℱ. -/
theorem spec {E₁ E₂ : SquareZeroAlgebraExtension f ℱ} (α : Hom E₁ E₂) :
    α.hom ≫ E₂.proj = E₁.proj ∧
      E₁.structureMap ≫ α.hom = E₂.structureMap ∧
        kernelHom α.hom α.comm_proj ≫ E₂.kernelIso.hom = E₁.kernelIso.hom :=
  sorry

/-- Identity morphisms of identity-base square-zero extensions. -/
def id (E : SquareZeroAlgebraExtension f ℱ) : Hom E E where
  hom := 𝟙 E.middle
  comm_proj := sorry
  comm_structure := sorry
  induces_id := sorry

/-- Composition of morphisms of identity-base square-zero extensions. -/
def comp {E₁ E₂ E₃ : SquareZeroAlgebraExtension f ℱ} (α : Hom E₁ E₂) (β : Hom E₂ E₃) :
    Hom E₁ E₃ where
  hom := α.hom ≫ β.hom
  comm_proj := sorry
  comm_structure := sorry
  induces_id := sorry

end Hom

/-- Identity morphisms of identity-base square-zero extensions. -/
abbrev idHom (E : SquareZeroAlgebraExtension f ℱ) : Hom E E :=
  Hom.id E

/-- The category of identity-base square-zero f⁻¹𝒪_B-algebra extensions of 𝒪_X by ℱ. -/
instance instCategory : Category (SquareZeroAlgebraExtension f ℱ) where
  Hom := Hom
  id := idHom
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The identity morphism of the category of extensions is `idHom`. -/
theorem idHom_eq (E : SquareZeroAlgebraExtension f ℱ) :
    𝟙 E = idHom E :=
  sorry

/-- `DQ_X(ℱ) ⟶ DQ_X(𝒢)` is the image of ℱ ⟶ 𝒢 under the right adjoint of the inclusion
of `DerivedQCoh X` into `D(𝒪_X)`, after placing modules in degree zero. -/
def dqMap {X : AlgebraicSpace S} [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    (inclusion X).rightAdjoint.obj
        ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj ℱ) ⟶
      (inclusion X).rightAdjoint.obj
        ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj 𝒢) :=
  (inclusion X).rightAdjoint.map
    ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).map φ)

/-- `dqMap φ` is `(inclusion X).rightAdjoint` applied to the degree-zero image of φ. -/
theorem dqMap_eq {X : AlgebraicSpace S} [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    dqMap φ =
      (inclusion X).rightAdjoint.map
        ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).map φ) :=
  sorry

end SquareZeroAlgebraExtension

end AlgebraicGeometry.AlgebraicSpace.Hom
