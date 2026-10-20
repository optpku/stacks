module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.GeometricallyIrreducible.RatFunc
import StacksCheckRecall

@[expose] public section

/-!
# Rational-function criterion for geometric irreducibility

Lemma 10.47.10 is a direct recall of the reusable rational-function field-extension criterion.
The shared owner exposes the coefficient-induced `RatFunc k → RatFunc K` map explicitly, so the
chapter entry does not depend on a scoped `Algebra (RatFunc k) (RatFunc K)` instance.

@stack 0G31
-/

/- Lemma 10.47.10 (Tag 0G31): geometric irreducibility is invariant under `RatFunc`. -/
@[stacks 0G31]
#check @AlgebraicGeometry.FieldExtension.GeometricallyIrreducible.RatFunc.iff

/- Lemma 10.47.10 (Tag 0G31): explicit named-algebra `Spec.map` spelling. -/
@[stacks 0G31]
#check @AlgebraicGeometry.FieldExtension.GeometricallyIrreducible.RatFunc.iff_algebraMap

end
