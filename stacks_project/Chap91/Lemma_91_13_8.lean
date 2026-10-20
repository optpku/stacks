/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.Lemma_91_13_8_Extension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibre chart of isomorphism classes of first-order ringed-topos solutions

In the identified-topoi diagram 91.13.0.1, isomorphism classes of solutions are
canonically parametrized by the fibre of `extOne_comap π fSharp` over the image
of the tautological class ξ.
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
variable (π : O_B' ⟶ O_B) [Sheaf.IsLocallySurjective π]
variable (hπ : KernelIdeal.IsSquareZero π)
variable (fSharp : O_B ⟶ O)
variable (G : SheafOfModules (ringSheaf J O))
variable (c :
    hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
      (restrictionAlong fSharp).obj G)

/-- Lemma 91.13.8 Let t : (Sh(B), O_B) ⟶ (Sh(B'), O_B'), J = Ker(t^♯),
f : (Sh(C), O) ⟶ (Sh(B), O_B), G, and c : J ⟶ G be as in 91.13.0.1.
Denote ξ ∈ Ext¹_{O_B}(NL_{O_B/O_B'}, J) the element corresponding to the
extension O_B' of O_B by J via Lemma 91.13.4. The set of isomorphism classes
of solutions is canonically bijective to the fibre of
Ext¹_O(NL_{O/O_B'}, G) ⟶ Ext¹_O(Lf^* NL_{O_B/O_B'}, G) over the image of ξ.
Here J is `hπ.targetModule (KernelIdeal.quotientComparison_isIso π)`, ξ is
`selfExtensionClass π hπ`, the Ext¹ groups are `Ext⁽1⁾(Q NL, Q(G[0]))`,
the displayed map is `extOne_comap π fSharp`, the image of ξ is
`extOne_map (extendCoeff π hπ fSharp G c) (selfExtensionClass π hπ)`, and
the fibre is `solutionExtFiber π hπ fSharp G c`. -/
@[stacks 0GQ9]
def isoClassFiberEquiv : IsoClass π hπ fSharp G c ≃ solutionExtFiber π hπ fSharp G c where
  toFun p := ⟨toExtClass π hπ fSharp G c p, sorry⟩
  invFun := ofFiber π hπ fSharp G c
  left_inv := sorry
  right_inv := sorry

/-- The fibre chart sends an isomorphism class to its Ext¹ class in the fibre. -/
theorem isoClassFiberEquiv_apply (p : IsoClass π hπ fSharp G c) :
    (isoClassFiberEquiv π hπ fSharp G c p).val = toExtClass π hπ fSharp G c p := sorry

/-- The inverse fibre chart is `ofFiber`. -/
theorem isoClassFiberEquiv_symm_apply (ζ : solutionExtFiber π hπ fSharp G c) :
    (isoClassFiberEquiv π hπ fSharp G c).symm ζ = ofFiber π hπ fSharp G c ζ := sorry

/-- Solutions exist if and only if the image of ξ lies in the image of restriction. -/
theorem isoClassFiberEquiv_nonempty_iff :
    Nonempty (IsoClass π hπ fSharp G c) ↔
      Nonempty (solutionExtFiber π hπ fSharp G c) := sorry

end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
