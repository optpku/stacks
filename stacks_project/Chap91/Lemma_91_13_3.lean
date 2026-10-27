/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.Lemma_91_13_3_Translate
public import stacks_project.Chap91.Lemma_91_13_3_IsoClass
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

/-!
# Principal homogeneous space of first-order ringed-topos solutions

If a diagram 91.13.0.1 admits at least one solution, isomorphism classes of
solutions are principal homogeneous under Ext⁽1⁾(Q NL_{O/O_B}, Q(𝒢[0])).
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace Solution

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and Ext must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O_B' O_B O : Sheaf J CommRingCat.{u}}
variable {π : O_B' ⟶ O_B} [Sheaf.IsLocallySurjective π]
variable {hπ : KernelIdeal.IsSquareZero π}
variable {fSharp : O_B ⟶ O}
variable {G : SheafOfModules (ringSheaf J O)}
variable {c :
    hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
      (restrictionAlong fSharp).obj G}

/-- Lemma 91.13.3 If there exists a solution to 91.13.0.1, then the set of
isomorphism classes of solutions is principal homogeneous under
Ext⁽1⁾_O(NL_{O/O_B}, 𝒢). Existence is the basepoint S0; the acting group is
Ext⁽1⁾(Q NL(fSharp), Q(𝒢[0])). -/
def isoClassEquiv (S0 : Solution π hπ fSharp G c) :
    Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)) ≃
      IsoClass π hπ fSharp G c where
  toFun ξ := ξ +ᵥ isoClassMk S0
  invFun p := p -ᵥ isoClassMk S0
  left_inv ξ := (addTorsor S0).vadd_vsub' ξ (isoClassMk S0)
  right_inv p := (addTorsor S0).vsub_vadd' p (isoClassMk S0)

/-- The based chart sends an Ext¹ class ξ to the translate of the basepoint. -/
theorem isoClassEquiv_apply (S0 : Solution π hπ fSharp G c)
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    isoClassEquiv S0 ξ = ξ +ᵥ isoClassMk S0 := rfl

/-- The zero Ext¹ class is sent to the class of the basepoint. -/
theorem isoClassEquiv_zero (S0 : Solution π hπ fSharp G c) :
    isoClassEquiv S0 0 = isoClassMk S0 := Solution.vadd_zero (isoClassMk S0)

/-- The inverse chart is torsor subtraction against the basepoint. -/
theorem isoClassEquiv_symm_apply (S0 : Solution π hπ fSharp G c)
    (p : IsoClass π hπ fSharp G c) :
    (isoClassEquiv S0).symm p = p -ᵥ isoClassMk S0 := rfl

/- Lemma 91.13.3 The representative data and the certificates for the common presentations
and pushout kernels expose the representability and pushout-kernel facts used in the source proof. -/
@[stacks 08UK] #check
  (SheafOfModules.RingedSite.FirstOrderThickening.Solution.isoClassEquivOf
    (π := π) (hπ := hπ) (fSharp := fSharp) (G := G) (c := c) :
    (∀ ξ : Ext⁽(1 : ℤ)⁾(
      DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)),
      TranslationData (π := π) (hπ := hπ) (c := c) ξ) →
    (∀ S T : Solution π hπ fSharp G c, Difference.Certificates S T) →
    Solution π hπ fSharp G c →
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) ≃
      IsoClass π hπ fSharp G c)

end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
