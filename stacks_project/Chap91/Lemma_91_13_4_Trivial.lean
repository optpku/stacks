/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.«91_10_5_1_TrivSqZeroExt»
public import stacks_project.Chap91.«91_13_0_1_Solution»
public import stacks_project.Chap91.Lemma_91_13_3

/-!
# Split square-zero solution of the identity ringed-topos diagram

The identity diagram 0 ⟶ 0 ⟶ O_B ⟶ O_B ⟶ 0 with zero kernel map 0 ⟶ G
admits the split solution whose middle ring sheaf is `trivSqZeroExt O G`,
i.e. the source's G ⊕ O.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.TrivSqZeroExt (trivSqZeroExt fst inl snd inr)

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

/-- The identity morphism of a commutative ring sheaf is square-zero. -/
theorem isSquareZero_id (O : Sheaf J CommRingCat.{u}) :
    KernelIdeal.IsSquareZero (𝟙 O) := sorry

/-- The unique map `Ker(id : O_B ⟶ O_B) ⟶ G` in the identity diagram. -/
def zeroKernelMap {O_B O : Sheaf J CommRingCat.{u}} (fSharp : O_B ⟶ O)
    (G : SheafOfModules (ringSheaf J O)) :
    (isSquareZero_id O_B).targetModule (KernelIdeal.quotientComparison_isIso (𝟙 O_B)) ⟶
      (restrictionAlong fSharp).obj G :=
  0

/-- `zeroKernelMap` is the zero morphism of `O_B`-modules. -/
theorem zeroKernelMap_eq_zero {O_B O : Sheaf J CommRingCat.{u}} (fSharp : O_B ⟶ O)
    (G : SheafOfModules (ringSheaf J O)) :
    zeroKernelMap fSharp G = 0 := sorry

/-- `zeroKernelMap` sends every kernel section to zero. -/
theorem zeroKernelMap_apply {O_B O : Sheaf J CommRingCat.{u}} (fSharp : O_B ⟶ O)
    (G : SheafOfModules (ringSheaf J O)) (U : Cᵒᵖ)
    (x : ((isSquareZero_id O_B).targetModule
      (KernelIdeal.quotientComparison_isIso (𝟙 O_B))).val.obj U) :
    (zeroKernelMap fSharp G).val.app U x = 0 := sorry

/-- The projection `O ⊕ G ⟶ O` is locally surjective. -/
instance instIsLocallySurjective_fst (O : Sheaf J CommRingCat.{u})
    (G : SheafOfModules (ringSheaf J O)) :
    Sheaf.IsLocallySurjective (fst O G) := sorry

/-- The projection `O ⊕ G ⟶ O` is a square-zero extension. -/
theorem isSquareZero_fst (O : Sheaf J CommRingCat.{u})
    (G : SheafOfModules (ringSheaf J O)) :
    KernelIdeal.IsSquareZero (fst O G) := sorry

/-- The inclusion `inr : G ⟶ O ⊕ G` lands in the kernel of `fst`. -/
theorem inr_mem_sectionIdeal (O : Sheaf J CommRingCat.{u})
    (G : SheafOfModules (ringSheaf J O)) (U : Cᵒᵖ) (m : G.val.obj U) :
    inr O G m ∈ KernelIdeal.sectionIdeal (fst O G) U := sorry

/-- B-linear identification of `Ker(O ⊕ G ⟶ O)` with `G`, via `snd` and `inr`. -/
def kernelIso_fst (O : Sheaf J CommRingCat.{u})
    (G : SheafOfModules (ringSheaf J O)) :
    (isSquareZero_fst O G).targetModule
      (KernelIdeal.quotientComparison_isIso (fst O G)) ≅ G where
  hom :=
    { val :=
        PresheafOfModules.homMk
          { app U :=
              AddCommGrpCat.ofHom <|
                AddMonoidHom.mk'
                  (fun x ↦
                    snd O G
                      (KernelIdeal.ιApp (fst O G) U
                        (((isSquareZero_fst O G).targetModuleForgetIso
                            (KernelIdeal.quotientComparison_isIso (fst O G))).hom.hom.app
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
                    ((isSquareZero_fst O G).targetModuleForgetIso
                          (KernelIdeal.quotientComparison_isIso (fst O G))).inv.hom.app
                      U ((KernelIdeal.sectionsIso (fst O G) U).inv
                        ⟨inr O G n, inr_mem_sectionIdeal O G U n⟩))
                  sorry
            naturality {_ _} _ := sorry }
          (fun _ _ _ ↦ sorry) }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- On a kernel section, `kernelIso_fst` is the second projection of `trivSqZeroExt`. -/
theorem kernelIso_fst_hom_apply (O : Sheaf J CommRingCat.{u})
    (G : SheafOfModules (ringSheaf J O)) (U : Cᵒᵖ)
    (x : ((isSquareZero_fst O G).targetModule
      (KernelIdeal.quotientComparison_isIso (fst O G))).val.obj U) :
    (kernelIso_fst O G).hom.val.app U x =
      snd O G
        (KernelIdeal.ιApp (fst O G) U
          (((isSquareZero_fst O G).targetModuleForgetIso
              (KernelIdeal.quotientComparison_isIso (fst O G))).hom.hom.app U x)) := sorry

/-- The inverse of `kernelIso_fst` is inclusion of `G` by `inr`. -/
theorem kernelIso_fst_inv_apply (O : Sheaf J CommRingCat.{u})
    (G : SheafOfModules (ringSheaf J O)) (U : Cᵒᵖ) (n : G.val.obj U) :
    (kernelIso_fst O G).inv.val.app U n =
      ((isSquareZero_fst O G).targetModuleForgetIso
            (KernelIdeal.quotientComparison_isIso (fst O G))).inv.hom.app
        U ((KernelIdeal.sectionsIso (fst O G) U).inv
          ⟨inr O G n, inr_mem_sectionIdeal O G U n⟩) := sorry

/-- The split solution of the identity diagram, with middle ring sheaf `trivSqZeroExt O G`. -/
def trivialSolution {O_B O : Sheaf J CommRingCat.{u}} (fSharp : O_B ⟶ O)
    (G : SheafOfModules (ringSheaf J O)) :
    Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G) where
  middle := trivSqZeroExt O G
  proj := fst O G
  structureMap := fSharp ≫ inl O G
  proj_locallySurjective := instIsLocallySurjective_fst O G
  proj_squareZero := isSquareZero_fst O G
  proj_quotient_isIso := KernelIdeal.quotientComparison_isIso (fst O G)
  commutes := sorry
  kernelIso := kernelIso_fst O G
  induces_c := sorry

/-- The carrier of the split solution is `trivSqZeroExt O G`. -/
theorem trivialSolution_middle {O_B O : Sheaf J CommRingCat.{u}} (fSharp : O_B ⟶ O)
    (G : SheafOfModules (ringSheaf J O)) :
    (trivialSolution fSharp G).middle = trivSqZeroExt O G := sorry

/-- The projection of the split solution is `fst`. -/
theorem trivialSolution_proj {O_B O : Sheaf J CommRingCat.{u}} (fSharp : O_B ⟶ O)
    (G : SheafOfModules (ringSheaf J O)) :
    (trivialSolution fSharp G).proj = fst O G := sorry

/-- The structure map of the split solution is `inl` after `fSharp`. -/
theorem trivialSolution_structureMap {O_B O : Sheaf J CommRingCat.{u}}
    (fSharp : O_B ⟶ O) (G : SheafOfModules (ringSheaf J O)) :
    (trivialSolution fSharp G).structureMap = fSharp ≫ inl O G := sorry

end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
