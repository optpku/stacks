/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.«90_15_0_2»
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap90.Example_90_15_3_Quotient

/-!
# Minimal versal formal objects and orbit-bijective differentials

A predeformation category satisfying Schlessinger's condition (S2) and possessing
a versal formal object has a minimal versal formal object whose differential is
bijective on `Derivation Λ k k`-orbits.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace FormalObject

/-- Lemma 90.15.4: if `p` is a predeformation category satisfying `HasSchlessingerS2`
and `ξ` is a minimal versal formal object of `p`, then
`BijectiveDifferentialOnOrbits ξ` holds. -/
@[stacks 06T8]
theorem bijectiveDifferentialOnOrbits_of_isMinimalVersal
    [Functor.IsPredeformationCategory p] [Functor.HasSchlessingerS2 p]
    (ξ : FormalObject p) [IsMinimalVersal ξ] :
    BijectiveDifferentialOnOrbits ξ := sorry

end FormalObject
