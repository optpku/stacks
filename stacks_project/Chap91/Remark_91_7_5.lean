/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Remark_91_7_5_Presentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Presentation chart of square-zero f⁻¹𝒪_S-algebra extensions of 𝒪_X by 𝒢

For an extension 0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0 as in Lemma 91.7.4, a sheaf of sets E
with a commutative triangle E ⟶ 𝒪_{X'} ⟶ 𝒪_X making f⁻¹𝒪_S[E] ⟶ 𝒪_X locally
surjective presents NL[f] by the two-term complex NL(α), and the induced map
J / J² ⟶ 𝒢 is the Ext¹ class of 𝒪_{X'} under the inverse of `extensionEquiv`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.NaiveCotangent
open TopologicalSpace
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback
open scoped CategoryTheory.Sheaf.FreeAlgebra

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Solution

variable {S X : RingedSpace.{u}} {f : X ⟶ S} {G : X.Modules}

/-- Remark 91.7.5 (1) For a square-zero extension 0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0 as in
Lemma 91.7.4, a sheaf of sets `E` and a lift `α' : E ⟶ i⁻¹𝒪_{X'}` yield a
commutative triangle `E ⟶ i⁻¹𝒪_{X'} ⟶ 𝒪_X`. If `α'` is locally surjective, then
the induced evaluation `f⁻¹𝒪_S[E] ⟶ 𝒪_X` is locally surjective. The source
example takes `E` to be the underlying sheaf of sets of `i⁻¹𝒪_{X'}` with
`α' = 𝟙`. -/
@[stacks 0GQ0, instance]
instance eval_assignOf_isLocallySurjective
    (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    [Sheaf.IsLocallySurjective α'] :
    Sheaf.IsLocallySurjective (eval E (assignOf sol E α')) := sorry

/-- Remark 91.7.5 (2) If `f⁻¹𝒪_S[E] ⟶ 𝒪_X` is locally surjective with kernel `J`,
then `NL[f] ≅ NL(α)` in the derived category, where `NL(α)` is the two-term
complex `J / J² ⟶ Ω_{f⁻¹𝒪_S[E] / f⁻¹𝒪_S} ⊗_{f⁻¹𝒪_S[E]} 𝒪_X`. -/
@[stacks 0GQ0]
def naiveCotangentIso (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    [Sheaf.IsLocallySurjective
      (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f) E α).right] :=
  Presentation.derivedComparisonIso E α

/-- The forward map of `naiveCotangentIso` is the canonical derived comparison. -/
theorem naiveCotangentIso_hom (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    [Sheaf.IsLocallySurjective
      (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f) E α).right] :
    (naiveCotangentIso E α).hom = Presentation.derivedComparison E α := sorry

/-- Remark 91.7.5 (3) The lift `α'` determines `f⁻¹𝒪_S[E] ⟶ i⁻¹𝒪_{X'}` and hence
`J / J² ⟶ 𝒢`, and the resulting `Ext¹` class of `NL(α) ≅ NL[f]` is the class of
`𝒪_{X'}` under the inverse of `extensionEquiv`. -/
@[stacks 0GQ0]
theorem extClass_eq_extensionEquiv_symm
    (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    [Sheaf.IsLocallySurjective
      (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f) E α).right]
    (hα : assignOf sol E α' = α) :
    extClass sol E α' α hα = (extensionEquiv f G).symm (isoClassMk sol) := sorry

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
