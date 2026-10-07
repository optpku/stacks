module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
variable [AlgebraicGeometry.IsImmersion f]

/- Lemma 29.20.16: an immersion of schemes is locally quasi-finite. -/
@[stacks 01TN] #check (AlgebraicGeometry.instLocallyQuasiFiniteOfIsImmersion (f := f) :
  AlgebraicGeometry.LocallyQuasiFinite f)

#check (inferInstance : AlgebraicGeometry.LocallyOfFiniteType f)
