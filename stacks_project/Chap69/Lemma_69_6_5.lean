module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import stacks_project.Chap69.Lemma_69_6_5_Quotient
public import stacks_project.Chap69.Lemma_69_6_5_Twist
public import stacks_project.Chap69.Lemma_69_6_5_Sections
public import stacks_project.Chap69.Lemma_69_6_5_Regular
public import stacks_project.Chap69.Lemma_69_6_5_Descent

/-!
# Lemma 69.6.5

For a scheme `S`, an algebraic space `W` over `S`, a finite group `G` acting
freely on `W`, a free quotient morphism `q : W ⟶ U`, and a character
`χ : G →* ℤˣ`, the sheaf `ℤ̲(χ)` of `ℤ`-modules on `U_étale` is locally free
of rank 1, and `H^0(W, F|_W)^χ ≅ H^0(U, F ⊗_ℤ ℤ̲(χ))` for every abelian
sheaf `F` on `U_étale`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {W U : AlgebraicSpace S} {G : Type u} [Group G] [Finite G]
variable (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)

/-- Lemma 69.6.5 (1): Let `S` be a scheme. Let `W` be an algebraic space over `S`.
Let `G` be a finite group acting freely on `W`. Let `U = W/G`, see Properties of
Spaces, Lemma 66.34.1, with quotient morphism `q : W ⟶ U`. Let `χ : G → {+1, -1}`
be a character. The sheaf of `ℤ`-modules `ℤ̲(χ)` on `U_étale` is locally free of
rank 1. -/
@[stacks 0727, instance]
instance integerCharacterSheaf_isFiniteLocallyFreeOfRankOne :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 (integerCharacterSheaf ρ q χ) :=
  sorry

/-- Lemma 69.6.5 (2): Let `S` be a scheme. Let `W` be an algebraic space over `S`.
Let `G` be a finite group acting freely on `W`. Let `U = W/G`, see Properties of
Spaces, Lemma 66.34.1, with quotient morphism `q : W ⟶ U`. Let `χ : G → {+1, -1}`
be a character. For every abelian sheaf `F` on `U_étale`,
`H^0(W, F|_W)^χ ≅ H^0(U, F ⊗_ℤ ℤ̲(χ))`. -/
@[stacks 0727]
noncomputable def integerCharacterSheaf_globalSections
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    characterInvariants (globalSectionsAction ρ q F) χ ≅
      (globalSections U).obj (tensorIntegerCharacter ρ q χ F) where
  hom := integerCharacterSheaf_globalSectionsHom ρ q χ F
  inv := integerCharacterSheaf_globalSectionsInv ρ q χ F
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of Lemma 69.6.5 (2) is `integerCharacterSheaf_globalSectionsHom`. -/
theorem integerCharacterSheaf_globalSections_hom
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (integerCharacterSheaf_globalSections ρ q χ F).hom =
      integerCharacterSheaf_globalSectionsHom ρ q χ F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
