module

public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.BaseChange.Comparison

@[expose] public section

open scoped TensorProduct

universe u

variable {A1 A2 : Type u} [CommRing A1] [CommRing A2] [Algebra A1 A2]

#check (CommAlgCat.TopologicallyFiniteType.includeLeftToCompletion :
  ∀ (I2 : Ideal A2) (B : Type u) [CommRing B] [Algebra A1 B],
    B →+* Algebra.TopologicallyFiniteType.completedBaseChange A1 I2 B)
