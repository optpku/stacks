module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.DerivedAdeq.Adjunction

/- Remark 46.10.2: the derived association and Zariski-restriction functors are
adjoint, and the unit on `Scheme.DerivedQCoh S` is invertible. -/
@[stacks 070W] #check (SheafOfModules.DerivedAdeq.adjunctionUnitIsIso :
  ∀ (S : AlgebraicGeometry.Scheme) (τ : AlgebraicGeometry.StandardTopology),
    CategoryTheory.IsIso (SheafOfModules.DerivedAdeq.adjunction S τ).unit)
