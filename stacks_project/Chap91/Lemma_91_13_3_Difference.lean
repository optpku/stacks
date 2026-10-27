/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.Difference
public import stacks_project.Chap91.Lemma_91_13_3_Translate

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.NaiveCotangent
open HomologicalComplex DerivedCategory
open Opposite TrivSqZeroExt
open scoped DerivedExt SheafOfModules.RingedSite
open scoped CategoryTheory.Sheaf.FreeAlgebra

noncomputable section

universe c v w

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace Solution

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and Ext must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] HasDerivedCategory.standard

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O_B' O_B O : Sheaf J CommRingCat.{w}}
variable {π : O_B' ⟶ O_B} [Sheaf.IsLocallySurjective π]
variable {hπ : KernelIdeal.IsSquareZero π}
variable {fSharp : O_B ⟶ O}
variable {G : SheafOfModules (ringSheaf J O)}
variable {c :
    hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
      (restrictionAlong fSharp).obj G}

namespace Difference
variable (S₁ S₂ : Solution π hπ fSharp G c)

/-- The conormal evaluation difference, using the common-presentation epimorphism theorem. -/
def conormalDifference :
    (Presentation.ofGenerators (generators S₁ S₂) (assignment S₁ S₂)).X (-1) ⟶ G :=
  conormalDifferenceOf S₁ S₂ (conormalComparison_epi S₁ S₂)

/-- The descended map recovers the back-minus-front evaluation difference. -/
theorem conormalComparison_comp_difference :
    conormalComparison S₁ S₂ ≫ conormalDifference S₁ S₂ = liftedDifference S₁ S₂ :=
  @Abelian.comp_epiDesc _ _ _ _ _ (conormalComparison S₁ S₂)
    (conormalComparison_epi S₁ S₂) _ (liftedDifference S₁ S₂) (kernel_comp_difference S₁ S₂)

/-- The extension class of the common-presentation difference. -/
def extClass : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  extClassOf S₁ S₂
    { epi := conormalComparison_epi S₁ S₂
      assignment := assignment_locallySurjective S₁ S₂
      evaluation := evaluation_locallySurjective S₁ S₂
      quasiIso := by
        -- Local instance justification (proof-local temporary data): toCanonicalMap_quasiIso consumes this fixed common-presentation evaluation certificate through its local-surjectivity class argument.
        letI := evaluation_locallySurjective S₁ S₂
        exact Presentation.toCanonicalMap_quasiIso (generators S₁ S₂) (assignment S₁ S₂) }

end Difference
end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
