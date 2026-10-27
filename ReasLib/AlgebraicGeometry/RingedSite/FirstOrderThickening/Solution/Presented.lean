/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.ExtPresentation
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.Translate
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.Difference

@[expose] public section
open CategoryTheory CategoryTheory.Sheaf
open SheafOfModules.RingedSite SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt
noncomputable section
universe c v w

namespace SheafOfModules.RingedSite.FirstOrderThickening.Solution

-- Pin the same derived-category instance as the existing translation owner.
-- Local instance justification (defeq pin): all Ext and presentation maps use the standard derived quotient at the independent coefficient universe.
attribute [local instance] HasDerivedCategory.standard

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O_B' O_B O : Sheaf J CommRingCat.{w}}
variable {π : O_B' ⟶ O_B} [IsLocallySurjective π]
variable {hπ : KernelIdeal.IsSquareZero π} {fSharp : O_B ⟶ O}
variable {G : SheafOfModules.{w} (ringSheaf J O)}
variable {c : hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
  (restrictionAlong fSharp).obj G}

/-- Translate using the actual locally-surjective presentation representing ξ. -/
def translatePresented
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (P : ExtOnePresentation fSharp G ξ) (sol : Solution π hπ fSharp G c) :
    Solution π hπ fSharp G c :=
  translateOfWith P.generators P.assignment P.conormalMap (hEval := P.locallySurjective) sol
    (translateKernelInclusion_isIso P.generators P.assignment P.conormalMap
      (hEval := P.locallySurjective) sol)

/-- The translated middle algebra is the existing fiber-product-presentation pushout. -/
theorem translatePresented_middle
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (P : ExtOnePresentation fSharp G ξ) (sol : Solution π hπ fSharp G c) :
    (translatePresented ξ P sol).middle =
      translateSheaf P.generators P.assignment P.conormalMap sol :=
  (translateOfWith_spec P.generators P.assignment P.conormalMap
    (hEval := P.locallySurjective) sol
    (translateKernelInclusion_isIso P.generators P.assignment P.conormalMap
      (hEval := P.locallySurjective) sol)).1

/-- Difference uses the actual comparison cube of two extensions, not the
subtraction of lift-independent chosen conormal maps. -/
def differencePresented (S₁ S₂ : Solution π hπ fSharp G c) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  Difference.extClassOf S₁ S₂
    { epi := Difference.conormalComparison_epi S₁ S₂
      assignment := Difference.assignment_locallySurjective S₁ S₂
      evaluation := Difference.evaluation_locallySurjective S₁ S₂
      quasiIso := @Presentation.toCanonicalMap_quasiIso _ _ _ _ _ _ _ _ _ _
        (Difference.generators S₁ S₂) (Difference.assignment S₁ S₂)
        (Difference.evaluation_locallySurjective S₁ S₂) }

/-- The difference is exactly the canonical common-presentation obstruction. -/
theorem differencePresented_eq (S₁ S₂ : Solution π hπ fSharp G c) :
    differencePresented S₁ S₂ = Difference.extClassOf S₁ S₂
    { epi := Difference.conormalComparison_epi S₁ S₂
      assignment := Difference.assignment_locallySurjective S₁ S₂
      evaluation := Difference.evaluation_locallySurjective S₁ S₂
      quasiIso := @Presentation.toCanonicalMap_quasiIso _ _ _ _ _ _ _ _ _ _
        (Difference.generators S₁ S₂) (Difference.assignment S₁ S₂)
        (Difference.evaluation_locallySurjective S₁ S₂) } := rfl

end SheafOfModules.RingedSite.FirstOrderThickening.Solution
