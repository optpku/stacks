module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AlternatingCech
public import stacks_project.Chap69.Definition_69_6_2_ExtensionByZero
public import stacks_project.Chap69.Definition_69_6_2_Koszul
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 69.6.2: The alternating Čech complex of a surjective étale morphism
and an abelian sheaf has terms Hom(K^n, F), with Hom computed in abelian sheaves
on the small étale site and K^n the exterior power of degree n + 1 of f_! ℤ̲. -/
@[stacks 0724] #check (AlgebraicGeometry.AlgebraicSpace.alternatingCechComplex :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] [Surjective f],
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} →
      CochainComplex AddCommGrpCat.{u + 1} ℕ)
