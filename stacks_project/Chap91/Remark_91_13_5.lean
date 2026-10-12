/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Remark_91_13_5_Presentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Presentation chart of square-zero f⁻¹O_B-algebra extensions of O by G

For an extension 0 ⟶ G ⟶ O' ⟶ O ⟶ 0 as in Lemma 91.13.4, a sheaf of sets E with a
commutative triangle E ⟶ O' ⟶ O making O_B[E] ⟶ O locally surjective presents
NL_{O / O_B} by the two-term complex NL(α), and the induced map J / J² ⟶ G is the
Ext¹ class of O' under the inverse of `extensionEquiv`.
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
variable {fSharp : O_B ⟶ O}
variable {G : SheafOfModules (ringSheaf J O)}

/-- Remark 91.13.5 (1) For a square-zero extension 0 ⟶ G ⟶ O' ⟶ O ⟶ 0 as in
Lemma 91.13.4, a sheaf of sets `E` and a lift `α' : E ⟶ O'` yield a commutative
triangle `E ⟶ O' ⟶ O`. If `α'` is locally surjective, then the induced evaluation
`O_B[E] ⟶ O` is locally surjective. The source example takes `E` to be the
underlying sheaf of sets of `O'` with `α' = 𝟙`. -/
@[stacks 0GQ6, instance]
instance eval_assignOf_isLocallySurjective
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle)
    [Sheaf.IsLocallySurjective α'] :
    Sheaf.IsLocallySurjective (eval E (assignOf S E α')) := sorry

/-- Remark 91.13.5 (2) If `O_B[E] ⟶ O` is locally surjective with kernel `J`, then
`NL_{O / O_B} ≅ NL(α)` in the derived category, where `NL(α)` is the two-term complex
`J / J² ⟶ Ω_{O_B[E] / O_B} ⊗_{O_B[E]} O`. -/
@[stacks 0GQ6]
def naiveCotangentIso (E : Sheaf J (Type u))
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation (Under.mk fSharp) E α).right] :=
  Presentation.derivedComparisonIso E α

/-- The forward map of `naiveCotangentIso` is the canonical derived comparison. -/
theorem naiveCotangentIso_hom (E : Sheaf J (Type u))
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation (Under.mk fSharp) E α).right] :
    (naiveCotangentIso E α).hom = Presentation.derivedComparison E α := sorry

/-- Remark 91.13.5 (3) The lift `α'` determines `O_B[E] ⟶ O'` and hence
`J / J² ⟶ G`, and the resulting `Ext¹` class of `NL(α) ≅ NL_{O / O_B}` is the class
of `O'` under the inverse of `extensionEquiv`. -/
@[stacks 0GQ6]
theorem extClass_eq_extensionEquiv_symm
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation (Under.mk fSharp) E α).right]
    (hα : assignOf S E α' = α) :
    extClass S E α' α hα = (extensionEquiv fSharp G).symm (isoClassMk S) := sorry

end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
