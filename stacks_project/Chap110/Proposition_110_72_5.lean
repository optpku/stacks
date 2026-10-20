/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.HomStack.NonAlgebraic
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.GroupoidsOver AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.HomStack
open scoped CategoryTheory.MonObj

universe u

/- Proposition 110.72.5: let `k` be an algebraically closed field which is not
an algebraic closure of a finite field, let `A0` be a nonzero abelian variety,
and let `X` be a regular projective flat family of geometrically connected
curves over `Spec(k⟦t⟧)` whose nodal special fibre has smooth components and a
loop of rational components. The Hom-stack into the classifying stack of the
constant abelian scheme is not algebraic. -/
@[stacks 0AFC] #check (AlgebraicGeometry.HomStack.not_isAlgebraic :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ¬ IsAlgebraicClosureOfFiniteField k)
    (A0 : SchemeOverField k) [GrpObj A0] [AbelianVariety A0] (hA0 : ¬ IsIso A0.hom)
    (X : Over (specPowerSeries k)) [Projective X.hom] [Flat X.hom]
    (h_connected : ∀ s : specPowerSeries k,
      GeometricallyConnected (X.hom.fiberToSpecResidueField s))
    (h_dim : ∀ s : specPowerSeries k, topologicalKrullDim (X.hom.fiber s) = 1)
    (h_regular : Scheme.Regular X.left)
    (h_loop : IsNodalWithRationalComponentLoop (specialFiber X)),
    ¬ AlgebraicStack (homStack X (classifyingTorsors (constantAbelianScheme A0))))
