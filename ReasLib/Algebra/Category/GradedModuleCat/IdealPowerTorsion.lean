/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.GradedModuleCat.Category
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Pro.Presentation
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace GradedModuleCat

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]

/-- The graded maps whose underlying kernel and cokernel are ideal-power torsion. -/
def idealPowerTorsionEquivalences (a : Ideal A) : MorphismProperty (GradedModuleCat 𝒜) :=
  fun _ N f ↦ Module.IsIdealPowerTorsion a (Hom.toLinearMap f).ker ∧
    Module.IsIdealPowerTorsion a (N.module ⧸ (Hom.toLinearMap f).range)

/-- A graded map is a torsion equivalence exactly when its kernel and cokernel are power torsion. -/
theorem idealPowerTorsionEquivalences_iff (a : Ideal A)
    {M N : GradedModuleCat 𝒜} (f : M ⟶ N) :
    idealPowerTorsionEquivalences 𝒜 a f ↔
      Module.IsIdealPowerTorsion a (Hom.toLinearMap f).ker ∧
        Module.IsIdealPowerTorsion a (N.module ⧸ (Hom.toLinearMap f).range) := sorry

/-- The localization functor inverting graded maps with ideal-power-torsion kernel and cokernel. -/
def idealPowerTorsionQuotient (a : Ideal A) :
    GradedModuleCat 𝒜 ⥤ (idealPowerTorsionEquivalences 𝒜 a).Localization :=
  (idealPowerTorsionEquivalences 𝒜 a).Q

variable {𝒜}

/-- The pro-object represented by a graded inverse system after ideal-power-torsion localization. -/
def torsionQuotientPro (a : Ideal A) (M : SequentialInverseSystem (GradedModuleCat 𝒜)) :
    Pro (idealPowerTorsionEquivalences 𝒜 a).Localization :=
  (Pro.lim.{u + 1, u + 1, 0, 0} ℕᵒᵖ).obj (M ⋙ idealPowerTorsionQuotient 𝒜 a)

end GradedModuleCat
