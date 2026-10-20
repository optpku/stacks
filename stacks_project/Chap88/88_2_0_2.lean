module

public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType
import StacksCheckRecall

@[expose] public section

universe v u

/- 88.2.0.2: the category of I-adically complete A-algebras B such that B ⧸ I B is of
finite type over A ⧸ I, with morphisms the A-algebra maps. -/
@[stacks 0AL4] #check (CommAlgCat.TopologicallyFiniteType.{v, u} :
  ∀ (R : Type u) [CommRing R], Ideal R → Type (max u (v + 1)))
