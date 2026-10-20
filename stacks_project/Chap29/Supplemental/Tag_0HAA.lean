module

public import ReasLib.AlgebraicGeometry.Scheme.Excellent
import StacksCheckRecall

/-!
# Characterization of excellent schemes

A scheme is excellent if and only if it is quasi-excellent and universally catenary.
-/

universe u

/- Lemma [Stacks 0HAA]: a scheme is excellent if and only if it is quasi-excellent and
universally catenary. -/
@[stacks 0HAA] #check (AlgebraicGeometry.Scheme.excellent_iff :
  ∀ X : AlgebraicGeometry.Scheme.{u}, AlgebraicGeometry.Scheme.Excellent X ↔
    AlgebraicGeometry.Scheme.QuasiExcellent X ∧ AlgebraicGeometry.UniversallyCatenary X)
