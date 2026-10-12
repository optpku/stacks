/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Forget.Additive

/-!
# Abelian and limit structure for differential graded modules

This leaf owns the structural instances used by homotopy, derived, and injective-object
applications. Coproduct and product instances are intentionally obtained from the stronger
all-colimits and all-limits owners.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

namespace DifferentialGradedAlgebra.GradedModule

/-- The category of graded modules in the tensor-morphism presentation is abelian. -/
instance instAbelian (𝒜 : DGA(𝒪)) : Abelian (GradedModule 𝒜) := sorry

/-- The category of graded modules has all colimits. -/
instance instHasColimits (𝒜 : DGA(𝒪)) : HasColimits (GradedModule 𝒜) := sorry

/-- Filtered colimits of graded modules are exact. -/
instance instAB5 (𝒜 : DGA(𝒪)) : AB5 (GradedModule 𝒜) := sorry

/-- The category of graded modules has all limits. -/
instance instHasLimits (𝒜 : DGA(𝒪)) : HasLimits (GradedModule 𝒜) := sorry

end DifferentialGradedAlgebra.GradedModule

namespace DifferentialGradedModule

/-- Lemma 24.13.2 (0FRJ): differential graded modules form an abelian category.  The
`Preadditive` field is the canonical degreewise structure already installed on DG modules. -/
@[stacks 0FRJ "abelian category"]
instance instAbelian (𝒜 : DGA(𝒪)) : Abelian (Mod(𝒜, d)) where
  toPreadditive := instPreadditive 𝒜
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- Lemma 24.13.2 (0FRJ): differential graded modules have all small colimits. -/
@[stacks 0FRJ "colimits"]
instance instHasColimits (𝒜 : DGA(𝒪)) : HasColimits (Mod(𝒜, d)) := sorry

/-- Lemma 24.13.2 (0FRJ): filtered colimits of differential graded modules are exact. -/
@[stacks 0FRJ "AB5"]
instance instAB5 (𝒜 : DGA(𝒪)) : AB5 (Mod(𝒜, d)) := sorry

/-- Exactness of sequential colimits of differential graded modules, exposed separately from
`AB5` so that small sequential diagrams remain inferable across universe levels. -/
@[stacks 0FRJ "exact sequential colimits"]
instance hasExactSequentialColimits (𝒜 : DGA(𝒪)) :
    HasExactColimitsOfShape ℕ (Mod(𝒜, d)) := sorry

/-- Lemma 24.13.2 (0FRJ): differential graded modules have all small limits. -/
@[stacks 0FRJ "limits"]
instance instHasLimits (𝒜 : DGA(𝒪)) : HasLimits (Mod(𝒜, d)) := sorry

/-- Lemma 24.13.2 (0FRJ): forgetting the differential preserves all small limits. -/
@[stacks 0FRJ "forgetful functor preserves limits"]
instance forgetToGradedPreservesLimits (𝒜 : DGA(𝒪)) :
    PreservesLimits (forgetToGraded 𝒜) := sorry

/-- Lemma 24.13.2 (0FRJ): forgetting the differential preserves all small colimits. -/
@[stacks 0FRJ "forgetful functor preserves colimits"]
instance forgetToGradedPreservesColimits (𝒜 : DGA(𝒪)) :
    PreservesColimits (forgetToGraded 𝒜) := sorry

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
