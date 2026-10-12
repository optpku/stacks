/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap69.Situation_69_16_1_GlobalSections
public import stacks_project.Chap72.Definition_72_4_1_Integral

/-!
# Global sections of an integral algebraic space

The ring of global sections of an integral algebraic space is a domain.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.4.4: Let `S` be a scheme. Let `X` be an integral algebraic space
over `S`. Then `Γ(X, 𝒪_X)` is a domain. -/
@[stacks 0BH2]
instance instIsDomain_globalSectionsRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsIntegral X] : IsDomain (globalSectionsRing X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
