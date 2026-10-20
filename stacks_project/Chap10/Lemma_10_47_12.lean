module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.GeometricallyIrreducible
import StacksCheckRecall

@[expose] public section

/-!
# Field-extension criterion for geometric irreducibility

@stack 0G33

Lemma 10.47.12 is a canonical recall.  Its field-extension form belongs under
`FieldExtension.GeometricallyIrreducible`, where the morphism is represented by
`FieldExtension.specMap` rather than a chapter-specific expansion of `Spec.map`.
-/

/- Lemma 10.47.12 (Tag 0G33): the relative separable closure is trivial. -/
@[stacks 0G33]
#check @AlgebraicGeometry.FieldExtension.GeometricallyIrreducible.iff_separableClosure_eq_bot

/- Lemma 10.47.12 (Tag 0G33): every separable element lies in the base field. -/
@[stacks 0G33]
#check @AlgebraicGeometry.FieldExtension.GeometricallyIrreducible.iff_forall_separable_mem_bot

end
