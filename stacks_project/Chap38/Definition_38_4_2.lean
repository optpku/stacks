module

import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissageAtAmbientPoint
import StacksCheckRecall

universe u

open AlgebraicGeometry

/- Definition 38.4.2: a one-step dévissage of `ℱ / X / S` at `x` consists of a one-step
dévissage over `f x`, maximal ambient-point fibre-support dimension, distinguished points with
singleton `π`-fibre, and a purely transcendental residue-field extension. -/
@[stacks 05H5] #check (AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint :
  {S : Scheme.{u}} → (X : CategoryTheory.Over S) → (ℱ : X.left.Modules) →
    [LocallyOfFiniteType X.hom] → [ℱ.IsQuasicoherent] → [ℱ.IsFiniteType] →
      (x : X.left) → Type (u + 1))
