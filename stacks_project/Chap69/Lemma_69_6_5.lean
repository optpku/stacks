module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.CharacterTwist
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
universe u
variable {S : Scheme.{u}} {W U : AlgebraicSpace S} {G : Type u} [Group G] [Finite G]
variable (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)

/- Lemma 69.6.5: semi-invariant sections are global sections of the character twist. -/
@[stacks 0727]
#check (AlgebraicGeometry.AlgebraicSpace.integerCharacterSheaf_globalSections ρ q χ :
  ∀ F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1},
    IntegerCharacter.invariants (globalSectionsAction ρ q F) χ ≅
      (globalSections U).obj (tensorIntegerCharacter ρ q χ F))

#check (AlgebraicGeometry.AlgebraicSpace.integerCharacterSheaf_isFiniteLocallyFreeOfRankOne
    ρ q χ : SheafOfModules.IsFiniteLocallyFreeOfRank 1 (integerCharacterSheaf ρ q χ))
