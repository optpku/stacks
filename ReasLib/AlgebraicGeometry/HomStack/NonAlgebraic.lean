module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.KrullDimension
public import ReasLib.FieldTheory.AlgebraicClosure.FiniteField
public import ReasLib.AlgebraicGeometry.Scheme.PowerSeries
public import ReasLib.AlgebraicGeometry.GroupScheme.ClassifyingStack
public import ReasLib.AlgebraicGeometry.Curve.RationalComponentLoop
public import ReasLib.AlgebraicGeometry.HomStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Effective
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-!
# Non-algebraicity of a mapping stack into a constant abelian classifying stack
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.GroupoidsOver AlgebraicGeometry.Scheme.Hom
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.HomStack

/-- Let `k` be an algebraically closed field which is not
an algebraic closure of a finite field, let `A0` be a nonzero abelian variety
over `k`, and let `X` be a regular scheme, projective and flat over
`S = specPowerSeries k`, whose fibres are geometrically connected curves and
whose special fibre is an at-worst-nodal curve with smooth irreducible
components whose dual graph contains a cycle of rational curves. Then the
Hom-stack `homStack X (classifyingTorsors (constantAbelianScheme A0))` is not
an algebraic stack. -/
@[stacks 0AFC]
theorem not_isAlgebraic {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ¬ IsAlgebraicClosureOfFiniteField k)
    (A0 : SchemeOverField k) [GrpObj A0] [AbelianVariety A0] (hA0 : ¬ IsIso A0.hom)
    (X : Over (specPowerSeries k)) [Projective X.hom] [Flat X.hom]
    (h_connected : ∀ s : specPowerSeries k,
      GeometricallyConnected (X.hom.fiberToSpecResidueField s))
    (h_dim : ∀ s : specPowerSeries k, topologicalKrullDim (X.hom.fiber s) = 1)
    (h_regular : Scheme.Regular X.left)
    (h_loop : IsNodalWithRationalComponentLoop (specialFiber X)) :
    ¬ AlgebraicStack (homStack X (classifyingTorsors (constantAbelianScheme A0))) :=
  sorry

/-- Over an algebraically closed field which is not an algebraic closure of a
finite field, let `A0` be a nonzero abelian variety and let `X` be a regular,
projective flat family of geometrically connected curves over `specPowerSeries k`
whose nodal special fibre has a loop of rational components. The Hom-stack from
`X` to the classifying stack of the constant abelian scheme associated to `A0`
has a non-effective formal object. -/
@[stacks 0AFD]
theorem exists_not_isEffective_formalObject {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ¬ IsAlgebraicClosureOfFiniteField k)
    (A0 : SchemeOverField k) [GrpObj A0] [AbelianVariety A0] (hA0 : ¬ IsIso A0.hom)
    (X : Over (specPowerSeries k)) [Projective X.hom] [Flat X.hom]
    (h_connected : ∀ s : specPowerSeries k,
      GeometricallyConnected (X.hom.fiberToSpecResidueField s))
    (h_dim : ∀ s : specPowerSeries k, topologicalKrullDim (X.hom.fiber s) = 1)
    (h_regular : Scheme.Regular X.left)
    (h_loop : IsNodalWithRationalComponentLoop (specialFiber X)) :
    ∃ ξ : FormalObject (homStack X (classifyingTorsors (constantAbelianScheme A0))),
      ¬ FormalObject.IsEffective ξ :=
  sorry

end AlgebraicGeometry.HomStack
