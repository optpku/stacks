module

public import ReasLib.AlgebraicGeometry.Scheme.GermProperty
import StacksCheckRecall

/- Definition 35.21.1 (1): a property of scheme germs is étale local when it is invariant
in both directions along every morphism étale at the selected source point. -/
@[stacks 04N1] #check
  (AlgebraicGeometry.GermProperty.IsEtaleLocal : AlgebraicGeometry.GermProperty → Prop)

/- Definition 35.21.1 (2): a property of scheme germs is smooth local when it is invariant
in both directions along every morphism smooth at the selected source point. -/
@[stacks 04N1] #check
  (AlgebraicGeometry.GermProperty.IsSmoothLocal : AlgebraicGeometry.GermProperty → Prop)
