/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExtendedCech
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Koszul.Functoriality
public import Mathlib.Algebra.Homology.Embedding.Extend

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.Koszul

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/-- The value of a power of a global section is the corresponding pointwise power. -/
theorem sectionPow_naturality (s : (unitModule J O).sections) (n : ℕ)
    (U V : Cᵒᵖ) (g : U ⟶ V) :
    (unitModule J O).val.map g (ExtendedCech.sectionValue s U ^ n) = ExtendedCech.sectionValue s V ^ n := sorry

/-- The global section obtained by taking a pointwise power of a global section. -/
noncomputable def sectionPow
    (s : (unitModule J O).sections) (n : ℕ) : (unitModule J O).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ ExtendedCech.sectionValue s U ^ n)
    (fun {U V} g ↦ sectionPow_naturality s n U V g)

/-- Evaluation of a powered global section is pointwise exponentiation. -/
theorem sectionPow_apply (s : (unitModule J O).sections) (n : ℕ) (U : Cᵒᵖ) :
    (sectionPow s n).val U = ExtendedCech.sectionValue s U ^ n := sorry

/-- The finite free family map for the `n`th powers of the chosen sections. -/
noncomputable def poweredFamilyMap
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    Arrow (ringedSiteModuleCategory J O) :=
  ExtendedCech.familyMap (fun i ↦ sectionPow (f i) n)

/-- The powered family map unfolds to the Čech family-map construction. -/
theorem poweredFamilyMap_def
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredFamilyMap f n = ExtendedCech.familyMap (fun i ↦ sectionPow (f i) n) := sorry

/-- Multiplication by a global section on a sheaf of modules. -/
noncomputable def globalSectionAction
    (s : (unitModule J O).sections) (M : ringedSiteModuleCategory J O) : M ⟶ M where
  val.app U := ModuleCat.ofHom
    (LinearMap.lsmul (O.obj.obj U) (M.val.obj U) (ExtendedCech.sectionValue s U))
  val.naturality _ := sorry

/-- The global-section action has the expected component on every object of the site. -/
theorem globalSectionAction_app
    (s : (unitModule J O).sections) (M : ringedSiteModuleCategory J O) (U : Cᵒᵖ) :
    (globalSectionAction s M).val.app U = ModuleCat.ofHom
      (LinearMap.lsmul (O.obj.obj U) (M.val.obj U) (ExtendedCech.sectionValue s U)) := sorry

/-- The diagonal endomorphism of the finite free module sheaf which multiplies generator `i`
by `f i`. -/
noncomputable def poweredFamilyStep
    {r : ℕ} (f : Fin r → (unitModule J O).sections) :
    (poweredFamilyMap f 1).left ⟶ (poweredFamilyMap f 1).left :=
  ((poweredFamilyMap f 1).left).freeHomEquiv.symm
    fun i ↦ SheafOfModules.sectionsMap
      (globalSectionAction (f i.down)
        (poweredFamilyMap f 1).left)
      (((poweredFamilyMap f 1).left).freeHomEquiv (𝟙 _) i)

/-- The powered family map, regarded as a linear form over the structure module. -/
noncomputable abbrev poweredLinearForm
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    Koszul.LinearForm O :=
  Over.mk ((unitModule J O).freeHomEquiv.symm
    (fun i : ULift.{u} (Fin r) ↦ sectionPow (f i.down) (n + 1)))

/-- The powered linear form uses exponent `n + 1` at zero-based stage `n`. -/
theorem poweredLinearForm_hom
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    (poweredLinearForm f n).hom = (poweredFamilyMap f (n + 1)).hom := sorry

/-- The diagonal free-module map intertwines the `(n + 2)`nd- and `(n + 1)`st-power
linear forms. -/
theorem poweredFamilyStep_comp
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredFamilyStep f ≫ (poweredLinearForm f n).hom =
      (poweredLinearForm f (n + 1)).hom := sorry

/-- The adjacent morphism from the `(n + 2)`nd-power linear form to the
`(n + 1)`st-power linear form. -/
noncomputable def poweredLinearFormStep
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredLinearForm f (n + 1) ⟶ poweredLinearForm f n :=
  Over.homMk (poweredFamilyStep f) (poweredFamilyStep_comp f n)

/-- The underlying map of an adjacent powered linear-form transition is the diagonal
free-module endomorphism. -/
theorem poweredLinearFormStep_left
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    (poweredLinearFormStep f n).left = poweredFamilyStep f := sorry

/-- The ordinary Koszul cochain complex on the `(n + 1)`st powers, placed in nonpositive
degrees by downward extension of the exterior-degree chain complex. -/
noncomputable def poweredKoszulChainStage
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    CochainComplex (ringedSiteModuleCategory J O) ℤ :=
  (Koszul.complex O (poweredLinearForm f n).hom).extend ComplexShape.embeddingDownNat

/-- The ordinary powered Koszul cochain model is the downward extension of its chain complex. -/
theorem poweredKoszulChainStage_def
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredKoszulChainStage f n =
      (Koszul.complex O (poweredLinearForm f n).hom).extend
        ComplexShape.embeddingDownNat := sorry

/-- The adjacent transition in the ordinary powered Koszul cochain tower. -/
noncomputable def poweredKoszulChainStep
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredKoszulChainStage f (n + 1) ⟶ poweredKoszulChainStage f n :=
  (ComplexShape.embeddingDownNat.extendFunctor
    (ringedSiteModuleCategory J O)).map (Koszul.map O (poweredLinearFormStep f n))

/-- The ordinary successor transition is the extension of the Koszul map induced by the
diagonal powered-family morphism. -/
theorem poweredKoszulChainStep_def
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredKoszulChainStep f n =
      (ComplexShape.embeddingDownNat.extendFunctor
        (ringedSiteModuleCategory J O)).map (Koszul.map O (poweredLinearFormStep f n)) := sorry

end SheafOfModules.RingedSite.Koszul
