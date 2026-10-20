module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Koszul.Augmentation
public import stacks_project.Chap69.Definition_69_6_2_Koszul

/-! Compatibility interface for the degree-zero trace Koszul augmentation. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.traceKoszulToConstantComponent :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] [Surjective f],
    (koszulComplex f).X 0 ⟶
      CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X))
