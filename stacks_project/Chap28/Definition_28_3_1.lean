module

public import Mathlib.AlgebraicGeometry.Properties
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 28.3.1: a scheme `X` is integral via the canonical mathlib predicate `IsIntegral X`;
this packages nonemptiness together with integrality of the section ring on every nonempty open,
hence in particular on every nonempty affine open. -/
@[stacks 01OK] #check
  (AlgebraicGeometry.IsIntegral : AlgebraicGeometry.Scheme.{u} → Prop)
