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
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.PowerSeries

/-! # Non-effectivity for a mapping stack into an abelian classifying stack -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.GroupoidsOver AlgebraicGeometry.Scheme.Hom
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.HomStack

/-- For a regular projective flat family of geometrically connected curves over
the spectrum of a power-series ring over an algebraically closed field, with a nodal special fibre
having smooth components and a loop of rational components, restriction of the
mapping stack into the classifying stack of a nonzero constant abelian variety
is not essentially surjective, provided the field is not an algebraic closure
of a finite field. -/
@[stacks 0AFB]
theorem not_essSurj_canonicalRestriction {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ¬ IsAlgebraicClosureOfFiniteField k)
    (A0 : SchemeOverField k) [GrpObj A0] [AbelianVariety A0] (hA0 : ¬ IsIso A0.hom)
    (X : Over (specPowerSeries k)) [Projective X.hom] [Flat X.hom]
    (h_connected : ∀ s : specPowerSeries k,
      GeometricallyConnected (X.hom.fiberToSpecResidueField s))
    (h_dim : ∀ s : specPowerSeries k, topologicalKrullDim (X.hom.fiber s) = 1)
    (h_regular : Scheme.Regular X.left)
    (h_loop : IsNodalWithRationalComponentLoop (specialFiber X)) :
    ¬ (FormalObject.powerSeriesRestriction
      (homStack X (classifyingTorsors (constantAbelianScheme A0)))).EssSurj :=
  sorry

end AlgebraicGeometry.HomStack
