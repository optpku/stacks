module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ResolutionProperty
import StacksCheckRecall

universe u

/- Lemma 36.36.2: if a scheme admits an ample invertible module, then it has the resolution
property. -/
@[stacks 0F87] #check
  (AlgebraicGeometry.Scheme.hasResolutionProperty_of_hasAmpleInvertibleModule :
    ∀ {X : AlgebraicGeometry.Scheme.{u}},
      AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule X →
        AlgebraicGeometry.Scheme.HasResolutionProperty X)
