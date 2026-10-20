module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.StructureMorphism

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- The structure morphism of the stack of coherent sheaves. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.forget :
  {S : Scheme.{u}} → {X B : AlgebraicSpace S} →
    (f : X ⟶ B) → [FinitePresentation f] →
      AlgebraicGeometry.AlgebraicSpace.CohStack.toGroupoids f ⟶
        AlgebraicGeometry.GroupScheme.Classifying.toGroupoids B)
