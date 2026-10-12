/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.DerivedAdeq.Adjunction

/- Remark 46.10.2: the derived association and Zariski-restriction functors are
adjoint, and the unit on `Scheme.DerivedQCoh S` is invertible. -/
@[stacks 070W] #check (SheafOfModules.DerivedAdeq.adjunctionUnitIsIso :
  ∀ (S : AlgebraicGeometry.Scheme) (τ : AlgebraicGeometry.StandardTopology),
    CategoryTheory.IsIso (SheafOfModules.DerivedAdeq.adjunction S τ).unit)
