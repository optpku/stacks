/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.AlgebraExtension
public import stacks_project.Chap91.Lemma_91_13_3
import StacksCheckRecall

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
variable {O_B O : Sheaf J CommRingCat.{u}}
variable (fSharp : O_B ⟶ O)
variable (G : SheafOfModules (ringSheaf J O))

/- Lemma 91.13.4 Let f : (Sh(C), O) ⟶ (Sh(B), O_B) be a morphism of ringed topoi
and G an O-module. Isomorphism classes of square-zero f⁻¹O_B-algebra extensions
0 ⟶ G ⟶ O' ⟶ O ⟶ 0, with identified kernel G, are canonically classified by
Ext¹_O of the relative naive cotangent complex with coefficients in G. The same-site
ring sheaf O_B denotes the inverse-image base ring sheaf. -/
@[stacks 0GQ5] #check
  (SheafOfModules.RingedSite.FirstOrderThickening.Solution.extensionEquiv fSharp G :
    Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)) ≃
      IsoClass (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))

end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
