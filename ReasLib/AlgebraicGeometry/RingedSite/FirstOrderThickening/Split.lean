/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TrivSqZeroExt
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.Solution

/-!
# Split square-zero solution of the identity ringed-topos diagram

The identity diagram 0 ⟶ 0 ⟶ O_B ⟶ O_B ⟶ 0 with zero kernel map 0 ⟶ G
admits the split solution whose middle ring sheaf is `trivSqZeroExt O G`,
with ring coordinate O and square-zero module coordinate G.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.TrivSqZeroExt (trivSqZeroExt fst inl snd inr)

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace Solution

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The identity morphism of a commutative ring sheaf is square-zero. -/
theorem isSquareZero_id (O : Sheaf J CommRingCat.{w}) :
    KernelIdeal.IsSquareZero (𝟙 O) :=
  (instIsFirstOrderThickeningId O).isSquareZero

/-- The unique map `Ker(id : O_B ⟶ O_B) ⟶ G` in the identity diagram. -/
def zeroKernelMap {O_B O : Sheaf J CommRingCat.{w}} (fSharp : O_B ⟶ O)
    (G : SheafOfModules.{w} (ringSheaf J O)) :
    (isSquareZero_id O_B).targetModule (KernelIdeal.quotientComparison_isIso (𝟙 O_B)) ⟶
      (restrictionAlong fSharp).obj G :=
  0

/-- `zeroKernelMap` is the zero morphism of `O_B`-modules. -/
theorem zeroKernelMap_eq_zero {O_B O : Sheaf J CommRingCat.{w}} (fSharp : O_B ⟶ O)
    (G : SheafOfModules.{w} (ringSheaf J O)) :
    zeroKernelMap fSharp G = 0 := sorry

/-- `zeroKernelMap` sends every kernel section to zero. -/
theorem zeroKernelMap_apply {O_B O : Sheaf J CommRingCat.{w}} (fSharp : O_B ⟶ O)
    (G : SheafOfModules.{w} (ringSheaf J O)) (U : Cᵒᵖ)
    (x : ((isSquareZero_id O_B).targetModule
      (KernelIdeal.quotientComparison_isIso (𝟙 O_B))).val.obj U) :
    (zeroKernelMap fSharp G).val.app U x = 0 := sorry

/-- The projection `O ⊕ G ⟶ O` is locally surjective. -/
instance instIsLocallySurjective_fst (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) :
    Sheaf.IsLocallySurjective (fst O G) := sorry

/-- The projection `O ⊕ G ⟶ O` is a square-zero extension. -/
theorem isSquareZero_fst (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) :
    KernelIdeal.IsSquareZero (fst O G) := sorry

/-- The inclusion `inr : G ⟶ O ⊕ G` lands in the kernel of `fst`. -/
theorem inr_mem_sectionIdeal (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) (U : Cᵒᵖ) (m : G.val.obj U) :
    inr O G m ∈ KernelIdeal.sectionIdeal (fst O G) U := sorry

set_option backward.privateInPublic true in
/-- The second coordinate of a section of the kernel of the split projection. -/
private def kernelFstHomApp (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) (U : Cᵒᵖ)
    (x : ((isSquareZero_fst O G).targetModule
      (KernelIdeal.quotientComparison_isIso (fst O G))).val.obj U) : G.val.obj U :=
  snd O G (KernelIdeal.ιApp (fst O G) U
    (((isSquareZero_fst O G).targetModuleForgetIso
      (KernelIdeal.quotientComparison_isIso (fst O G))).hom.hom.app U x))

set_option backward.privateInPublic true in
/-- The second-coordinate map on the kernel preserves addition. -/
private theorem kernelFstHom_add (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) (U : Cᵒᵖ)
    (x y : ((isSquareZero_fst O G).targetModule
      (KernelIdeal.quotientComparison_isIso (fst O G))).val.obj U) :
    kernelFstHomApp O G U (x + y) =
      kernelFstHomApp O G U x + kernelFstHomApp O G U y := sorry

set_option backward.privateInPublic true in
/-- The additive second-coordinate map on a section of the split kernel. -/
private def kernelFstHomComponent (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) (U : Cᵒᵖ) :
    ((isSquareZero_fst O G).targetModule
      (KernelIdeal.quotientComparison_isIso (fst O G))).val.presheaf.obj U ⟶
      G.val.presheaf.obj U :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' (kernelFstHomApp O G U) (kernelFstHom_add O G U))

set_option backward.privateInPublic true in
/-- The second-coordinate maps on the split kernel commute with restrictions. -/
private theorem kernelFstHom_naturality (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) {U V : Cᵒᵖ} (rho : U ⟶ V) :
    ((isSquareZero_fst O G).targetModule
      (KernelIdeal.quotientComparison_isIso (fst O G))).val.presheaf.map rho ≫
        kernelFstHomComponent O G V =
      kernelFstHomComponent O G U ≫ G.val.presheaf.map rho := sorry

set_option backward.privateInPublic true in
/-- The second-coordinate map on the split kernel is O-linear. -/
private theorem kernelFstHom_smul (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) (U : Cᵒᵖ) (r : O.obj.obj U)
    (x : ((isSquareZero_fst O G).targetModule
      (KernelIdeal.quotientComparison_isIso (fst O G))).val.obj U) :
    kernelFstHomApp O G U (r • x) = r • kernelFstHomApp O G U x := sorry

set_option backward.privateInPublic true in
/-- Projection of the kernel of the split extension onto its module coordinate. -/
private def kernelFstHom (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) :
    (isSquareZero_fst O G).targetModule
      (KernelIdeal.quotientComparison_isIso (fst O G)) ⟶ G where
  val := PresheafOfModules.homMk
    { app := kernelFstHomComponent O G
      naturality {_ _} rho := kernelFstHom_naturality O G rho }
    (kernelFstHom_smul O G)

set_option backward.privateInPublic true in
/-- Inclusion of a module section into the descended kernel of the split projection. -/
private def kernelFstInvApp (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) (U : Cᵒᵖ) (n : G.val.obj U) :
    ((isSquareZero_fst O G).targetModule
      (KernelIdeal.quotientComparison_isIso (fst O G))).val.obj U :=
  ((isSquareZero_fst O G).targetModuleForgetIso
    (KernelIdeal.quotientComparison_isIso (fst O G))).inv.hom.app U
      ((KernelIdeal.sectionsIso (fst O G) U).inv
        ⟨inr O G n, inr_mem_sectionIdeal O G U n⟩)

set_option backward.privateInPublic true in
/-- Inclusion into the split kernel preserves addition. -/
private theorem kernelFstInv_add (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) (U : Cᵒᵖ) (x y : G.val.obj U) :
    kernelFstInvApp O G U (x + y) =
      kernelFstInvApp O G U x + kernelFstInvApp O G U y := sorry

set_option backward.privateInPublic true in
/-- The additive inclusion of module sections into the split kernel. -/
private def kernelFstInvComponent (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) (U : Cᵒᵖ) :
    G.val.presheaf.obj U ⟶ ((isSquareZero_fst O G).targetModule
      (KernelIdeal.quotientComparison_isIso (fst O G))).val.presheaf.obj U :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' (kernelFstInvApp O G U) (kernelFstInv_add O G U))

set_option backward.privateInPublic true in
/-- Inclusion into the split kernel commutes with restrictions. -/
private theorem kernelFstInv_naturality (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) {U V : Cᵒᵖ} (rho : U ⟶ V) :
    G.val.presheaf.map rho ≫ kernelFstInvComponent O G V =
      kernelFstInvComponent O G U ≫ ((isSquareZero_fst O G).targetModule
        (KernelIdeal.quotientComparison_isIso (fst O G))).val.presheaf.map rho := sorry

set_option backward.privateInPublic true in
/-- Inclusion into the split kernel is O-linear. -/
private theorem kernelFstInv_smul (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) (U : Cᵒᵖ) (r : O.obj.obj U)
    (x : G.val.obj U) :
    kernelFstInvApp O G U (r • x) = r • kernelFstInvApp O G U x := sorry

set_option backward.privateInPublic true in
/-- Inclusion of the module coordinate into the kernel of the split extension. -/
private def kernelFstInv (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) :
    G ⟶ (isSquareZero_fst O G).targetModule
      (KernelIdeal.quotientComparison_isIso (fst O G)) where
  val := PresheafOfModules.homMk
    { app := kernelFstInvComponent O G
      naturality {_ _} rho := kernelFstInv_naturality O G rho }
    (kernelFstInv_smul O G)

set_option backward.privateInPublic true in
/-- Projection followed by inclusion is the identity on the split kernel. -/
private theorem kernelFstHom_inv_id (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) :
    kernelFstHom O G ≫ kernelFstInv O G = 𝟙 _ := sorry

set_option backward.privateInPublic true in
/-- Inclusion followed by projection is the identity on the coefficient module. -/
private theorem kernelFstInv_hom_id (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) :
    kernelFstInv O G ≫ kernelFstHom O G = 𝟙 G := sorry

set_option backward.privateInPublic true in
/-- The kernel of the split projection is O-linearly isomorphic to the coefficient module,
by second-coordinate projection and module-coordinate inclusion. -/
def kernelIso_fst (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) :
    (isSquareZero_fst O G).targetModule
      (KernelIdeal.quotientComparison_isIso (fst O G)) ≅ G where
  hom := kernelFstHom O G
  inv := kernelFstInv O G
  hom_inv_id := kernelFstHom_inv_id O G
  inv_hom_id := kernelFstInv_hom_id O G

/-- On a kernel section, `kernelIso_fst` is the second projection of `trivSqZeroExt`. -/
theorem kernelIso_fst_hom_apply (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) (U : Cᵒᵖ)
    (x : ((isSquareZero_fst O G).targetModule
      (KernelIdeal.quotientComparison_isIso (fst O G))).val.obj U) :
    (kernelIso_fst O G).hom.val.app U x =
      snd O G
        (KernelIdeal.ιApp (fst O G) U
          (((isSquareZero_fst O G).targetModuleForgetIso
              (KernelIdeal.quotientComparison_isIso (fst O G))).hom.hom.app U x)) := sorry

/-- The inverse of `kernelIso_fst` is inclusion of `G` by `inr`. -/
theorem kernelIso_fst_inv_apply (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (ringSheaf J O)) (U : Cᵒᵖ) (n : G.val.obj U) :
    (kernelIso_fst O G).inv.val.app U n =
      ((isSquareZero_fst O G).targetModuleForgetIso
            (KernelIdeal.quotientComparison_isIso (fst O G))).inv.hom.app
        U ((KernelIdeal.sectionsIso (fst O G) U).inv
          ⟨inr O G n, inr_mem_sectionIdeal O G U n⟩) := sorry

set_option backward.privateInPublic true in
/-- The structure map of the split extension commutes with its projection. -/
private theorem trivialSolution_commutes {O_B O : Sheaf J CommRingCat.{w}}
    (fSharp : O_B ⟶ O) (G : SheafOfModules.{w} (ringSheaf J O)) :
    (fSharp ≫ inl O G) ≫ fst O G = 𝟙 O_B ≫ fSharp := sorry

set_option backward.privateInPublic true in
/-- The split structure map induces the zero map from the kernel of the identity. -/
private theorem trivialSolution_induces_c {O_B O : Sheaf J CommRingCat.{w}}
    (fSharp : O_B ⟶ O) (G : SheafOfModules.{w} (ringSheaf J O)) :
    kernelMapOf (𝟙 O_B) (isSquareZero_id O_B) fSharp (fst O G) (isSquareZero_fst O G)
        (KernelIdeal.quotientComparison_isIso (fst O G)) (fSharp ≫ inl O G)
        (trivialSolution_commutes fSharp G) ≫
      (restrictionAlong fSharp).map (kernelIso_fst O G).hom = zeroKernelMap fSharp G := sorry

set_option backward.privateInPublic true in
/-- The split solution of the identity diagram, with middle ring sheaf `trivSqZeroExt O G`. -/
def trivialSolution {O_B O : Sheaf J CommRingCat.{w}} (fSharp : O_B ⟶ O)
    (G : SheafOfModules.{w} (ringSheaf J O)) :
    Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G) where
  middle := trivSqZeroExt O G
  proj := fst O G
  structureMap := fSharp ≫ inl O G
  proj_locallySurjective := instIsLocallySurjective_fst O G
  proj_squareZero := isSquareZero_fst O G
  proj_quotient_isIso := KernelIdeal.quotientComparison_isIso (fst O G)
  commutes := trivialSolution_commutes fSharp G
  kernelIso := kernelIso_fst O G
  induces_c := trivialSolution_induces_c fSharp G

/-- The carrier of the split solution is `trivSqZeroExt O G`. -/
theorem trivialSolution_middle {O_B O : Sheaf J CommRingCat.{w}} (fSharp : O_B ⟶ O)
    (G : SheafOfModules.{w} (ringSheaf J O)) :
    (trivialSolution fSharp G).middle = trivSqZeroExt O G := sorry

/-- The projection of the split solution is `fst`. -/
theorem trivialSolution_proj {O_B O : Sheaf J CommRingCat.{w}} (fSharp : O_B ⟶ O)
    (G : SheafOfModules.{w} (ringSheaf J O)) :
    (trivialSolution fSharp G).proj = fst O G := sorry

/-- The structure map of the split solution is `inl` after `fSharp`. -/
theorem trivialSolution_structureMap {O_B O : Sheaf J CommRingCat.{w}}
    (fSharp : O_B ⟶ O) (G : SheafOfModules.{w} (ringSheaf J O)) :
    (trivialSolution fSharp G).structureMap = fSharp ≫ inl O G := sorry

end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
