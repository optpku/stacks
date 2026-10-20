module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Multicross
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Definition 53.16.2: the multicross singularity predicate for a closed point. -/
@[stacks 0C1W] #check (AlgebraicGeometry.SchemeOverField.isMulticrossSingularity :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) (x : X.left), Prop)

/- The ordinary-double-point specialization is the two-branch case. -/
#check (ordinaryDoublePoint_iff_multicrossPoint_two :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) (x : X.left),
    isOrdinaryDoublePoint X x ↔ isMulticrossPoint X x 2)

end AlgebraicGeometry.SchemeOverField
