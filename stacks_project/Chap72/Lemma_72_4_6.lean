module

public import ReasLib.RingTheory.Normal.Ring
public import stacks_project.Chap66.Lemma_66_25_4_Normal
public import stacks_project.Chap69.Situation_69_16_1_GlobalSections
public import stacks_project.Chap72.Definition_72_4_1_Integral

/-!
# Global sections of a normal integral algebraic space

The ring of global sections of a normal integral algebraic space is a normal domain.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.4.6: Let `S` be a scheme. Let `X` be a normal integral algebraic space
over `S`. Then `Γ(X, 𝒪_X)` is a normal domain. -/
@[stacks 0BH3]
instance instIsNormalRing_globalSectionsRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsNormal X] [IsIntegral X] : IsNormalRing (globalSectionsRing X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
