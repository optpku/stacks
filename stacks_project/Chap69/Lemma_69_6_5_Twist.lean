module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.CharacterTwist
public import stacks_project.Chap69.Definition_69_6_2_Koszul
public import stacks_project.Chap69.Lemma_69_6_3_DerivedSections

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
universe u
variable {S : Scheme.{u}} {W U : AlgebraicSpace S} {G : Type u} [Group G] [Finite G]
variable (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)

#check (AlgebraicGeometry.AlgebraicSpace.integerCharacterSheaf ρ q χ :
  SheafOfModules.{u + 1} (integerRingSheaf U))

#check (AlgebraicGeometry.AlgebraicSpace.integerCharacterSheaf_toSheaf ρ q χ :
  (SheafOfModules.toSheaf (integerRingSheaf U)).obj (integerCharacterSheaf ρ q χ) ≅
    integerCharacterAbelianSheaf ρ q χ)
