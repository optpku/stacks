/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Associated
import Mathlib.Tactic.CrossRefAttribute

/-!
# Standard-open formula for the canonical associated-module shift comparison

The underlying morphism `canonicalHom` and its degree-preservation input are owned by
`Twist.Associated` under Stacks tag `01MQ`. This file proves the standard-open formula and
packages that morphism as the canonical `ShiftComparison` used by downstream geometry.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Proj.AssociatedModule.ShiftComparison

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]
variable [DirectSum.Decomposition ℳ]

/-- On a positive standard open, `canonicalHom` sends a pure tensor of homogeneous
fractions to the fraction represented by their localized scalar action. -/
@[stacks 0B5R "standard-open formula for the canonical shift comparison"]
theorem canonicalHom_standardOpen
    {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (k : ℤ)
    (x : away 𝒜 ℳ f)
    (y : away 𝒜
      (GradedModule.shiftGrading
        (DirectSum.Decomposition.natToIntGrading 𝒜) k) f) :
    ∃ z : away 𝒜 (GradedModule.shiftGrading ℳ k) f,
        (z : LocalizedModule.Away (f : A) M) =
            (y : LocalizedModule.Away (f : A) A) •
              (x : LocalizedModule.Away (f : A) M) ∧
          (((canonicalHom 𝒜 ℳ k).val.app
              (op (Proj.basicOpen 𝒜 (f : A)))).hom
            (tensorSection (Proj 𝒜).sheaf
              (op (Proj.basicOpen 𝒜 (f : A)))
              (awaySection 𝒜 ℳ f hd x)
              (awaySection 𝒜
                (GradedModule.shiftGrading
                  (DirectSum.Decomposition.natToIntGrading 𝒜) k) f hd y))) =
            awaySection 𝒜 (GradedModule.shiftGrading ℳ k) f hd z := sorry

/-- The canonical associated-module shift comparison, usable without supplying an external
comparison package. -/
@[stacks 0B5R "canonical associated-module shift comparison"]
noncomputable def canonical : ShiftComparison 𝒜 ℳ :=
  ShiftComparison.ofHom 𝒜 ℳ (canonicalHom 𝒜 ℳ)
    (canonicalHom_standardOpen 𝒜 ℳ)

end AlgebraicGeometry.Proj.AssociatedModule.ShiftComparison
