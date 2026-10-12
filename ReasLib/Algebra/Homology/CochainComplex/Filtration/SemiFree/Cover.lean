/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.SemiFree.Construction

@[expose] public section

/-!
# Two-Step Semi-Free Covers

This leaf packages the elementary covers of differential graded modules whose
sources are two-step semi-free.  They are useful inputs for iterative
resolution constructions, independently of any particular totalization.
-/

open CategoryTheory
open HomologicalComplex

noncomputable section

universe u

namespace CochainComplex

variable {A : Type u} [Ring A]

/-- A two-step semi-free cover of a differential graded `A`-module is a map from the middle
term of an admissible short exact sequence with shifted-free end terms.  The map is
degreewise epic and lifts every cycle. -/
structure TwoStepSemiFreeCover (M : ModuleCat.DGMod A) where
  /-- The two-step semi-free presentation of the source. -/
  sequence : ShortComplex (ModuleCat.DGMod A)
  /-- The presentation is admissibly short exact after forgetting differentials. -/
  isAdmissibleShortExact :
    IsAdmissibleShortExact (dgModuleUnderlyingGradedHomSystem (A := A)) sequence
  /-- The left term of the presentation is a direct sum of shifted free modules. -/
  leftIsDirectSumOfShiftedFree : IsDirectSumOfShiftedFree sequence.X₁
  /-- The right term of the presentation is a direct sum of shifted free modules. -/
  rightIsDirectSumOfShiftedFree : IsDirectSumOfShiftedFree sequence.X₃
  /-- The cover map from the middle term to the target. -/
  π : sequence.X₂ ⟶ M
  /-- The cover map is epic in every cochain degree. -/
  degreewiseEpi : ∀ n : ℤ, Epi (π.f n)
  /-- The cover map is epic on cycles in every cochain degree. -/
  cyclesEpi : ∀ n : ℤ, Epi (cyclesMap π n)

namespace TwoStepSemiFreeCover

/-- The source of a two-step semi-free cover. -/
abbrev complex {M : ModuleCat.DGMod A} (C : TwoStepSemiFreeCover M) : ModuleCat.DGMod A :=
  C.sequence.X₂

/-- The source of a two-step semi-free cover has a semi-free filtration. -/
theorem hasSemiFreeFiltration {M : ModuleCat.DGMod A} (C : TwoStepSemiFreeCover M) :
    HasSemiFreeFiltration C.complex := sorry

/-- The degree components of a two-step semi-free cover are epic. -/
instance {M : ModuleCat.DGMod A} (C : TwoStepSemiFreeCover M) (n : ℤ) : Epi (C.π.f n) :=
  C.degreewiseEpi n

/-- The maps on cycles induced by a two-step semi-free cover are epic. -/
instance {M : ModuleCat.DGMod A} (C : TwoStepSemiFreeCover M) (n : ℤ) :
    Epi (cyclesMap C.π n) :=
  C.cyclesEpi n

/-- The cover map of a two-step semi-free cover is epic as a morphism of differential graded
modules. -/
instance {M : ModuleCat.DGMod A} (C : TwoStepSemiFreeCover M) : Epi C.π := sorry

end TwoStepSemiFreeCover

end CochainComplex
