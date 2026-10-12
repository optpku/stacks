/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_2_1_WeakAss

/-!
# Weakly associated locus of a module on an algebraic space

The set of weakly associated points of an `𝒪_X`-module, as the points of `|X|`
satisfying the étale-stalk weak-association predicate of Lemma 71.2.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The set of weakly associated points of an `𝒪_X`-module. -/
def weakAss (F : X.Modules) : Set (Points X) :=
  etaleStalkWeakAss F

/-- Membership in `F.weakAss` is the étale-stalk weakly-associated-point
predicate. -/
theorem mem_weakAss_iff (F : X.Modules) (x : Points X) :
    x ∈ F.weakAss ↔ etaleStalkWeakAss F x :=
  sorry

/-- For a quasi-coherent module, membership in `F.weakAss` is equivalent to weak
association on some étale scheme chart. -/
theorem mem_weakAss_iff_existsEtaleWeakAss (F : X.Modules) [F.IsQuasicoherent]
    (x : Points X) :
    x ∈ F.weakAss ↔ existsEtaleWeakAss F x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
