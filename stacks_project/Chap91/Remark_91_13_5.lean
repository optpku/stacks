/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.AlgebraExtension.Presentation
import StacksCheckRecall

/-!
# Polynomial presentations and classes of square-zero algebra extensions

The base ring sheaf represents f⁻¹O_B. A lift of generators to a square-zero extension
induces a conormal map whose derived class classifies that extension.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt SheafOfModules.RingedSite
open scoped CategoryTheory.Sheaf.FreeAlgebra

noncomputable section

universe u

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
variable {fSharp : O_B ⟶ O}
variable {G : SheafOfModules (ringSheaf J O)}

/- Remark 91.13.5 (1) A locally surjective lift gives a polynomial presentation.
The underlying set sheaf of the middle ring sheaf with its identity lift is an example. -/
@[stacks 0GQ6]
#check (SheafOfModules.RingedSite.FirstOrderThickening.Solution.eval_assignOf_isLocallySurjective :
  (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G)) →
  (E : Sheaf J (Type u)) → (α' : E ⟶ (sheafForget J).obj S.middle) →
  [Sheaf.IsLocallySurjective α'] →
  Sheaf.IsLocallySurjective (eval E (assignOf S E α')))

/- Remark 91.13.5 (2) A locally surjective polynomial evaluation presents the canonical
naive cotangent complex by the two-term complex J / J² ⟶ Ω ⊗ O. -/
@[stacks 0GQ6]
#check (SheafOfModules.RingedSite.NaiveCotangent.Presentation.derivedComparisonIso.{u, u, u, u + 1}
  (B := Under.mk fSharp) :
  (E : Sheaf J (Type u)) →
  (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp)) →
  [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation (Under.mk fSharp) E α).right] →
  CategoryTheory.Iso.{u + 1, u + 1}
    (DerivedCategory.Q.{u + 1}.obj (Presentation.ofGenerators (B := Under.mk fSharp) E α))
    (DerivedCategory.Q.{u + 1}.obj (NaiveCotangent.obj O_B (Under.mk fSharp))))

#check (SheafOfModules.RingedSite.NaiveCotangent.Presentation.derivedComparisonIso_hom
  (B := Under.mk fSharp) :
  (E : Sheaf J (Type u)) →
  (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp)) →
  [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation (Under.mk fSharp) E α).right] →
  (Presentation.derivedComparisonIso E α).hom = Presentation.derivedComparison E α)

/- Remark 91.13.5 (3) The induced conormal map J / J² ⟶ G determines precisely the
class of the extension under the inverse of the classification equivalence. -/
@[stacks 0GQ6]
#check (SheafOfModules.RingedSite.FirstOrderThickening.Solution.extClass_eq_extensionEquiv_symm :
  (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G)) →
  (E : Sheaf J (Type u)) → (α' : E ⟶ (sheafForget J).obj S.middle) →
  (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp)) →
  [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation (Under.mk fSharp) E α).right] →
  (hα : assignOf S E α' = α) →
  extClass S E α' α hα = (extensionEquiv fSharp G).symm (isoClassMk S))
