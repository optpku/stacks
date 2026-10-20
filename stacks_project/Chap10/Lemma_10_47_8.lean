module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.GeometricallyIrreducible
import StacksCheckRecall

@[expose] public section

/-!
# Algebraic-closure criterion for field extensions

Lemma 10.47.8 is the field-extension specialization of a reusable criterion.  The shared owner
uses `FieldExtension.specMap`, avoiding a chapter-local copy of the affine `Spec.map` spelling.

@stack 037P
-/

/- Lemma 10.47.8 (Tag 037P). -/
@[stacks 037P]
#check @AlgebraicGeometry.FieldExtension.GeometricallyIrreducible.of_algebraicClosure_eq_bot

end
