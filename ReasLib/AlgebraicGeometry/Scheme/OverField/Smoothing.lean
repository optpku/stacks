module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Flat smoothings of local complete intersection curves with isolated singularities
-/

@[expose]
public section

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A proper local complete intersection scheme over a field, of dimension at most one
and smooth away from finitely many points, admits a flat projective family over the
power series ring with smooth generic fibre and special fibre isomorphic to the
original scheme over the field. The special fibre is the pullback along the constant
coefficient map, and the generic fibre is taken at the generic point of the spectrum
of the power series ring. -/
@[stacks 0E7Y]
theorem exists_flat_projective_smoothing {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [IsLocalCompleteIntersectionOver k X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hns : {x : X.left | ¬ X.hom.SmoothAt x}.Finite) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of (PowerSeries k)))
      (_ : Projective f) (_ : Flat f)
      (e : Over.mk (pullback.snd f (Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff))) ≅ X),
      Smooth (f.fiberToSpecResidueField
        (genericPoint (Spec (CommRingCat.of (PowerSeries k))))) :=
  sorry

/-- A separated finite-type local complete intersection scheme over a field, of dimension
at most one and smooth away from finitely many points, admits a flat separated finite-type
family over the power series ring with smooth generic fibre and special fibre isomorphic
to the original scheme over the field. The special fibre is the pullback along the constant
coefficient map, and the generic fibre is taken at the generic point of the spectrum of
the power series ring. -/
@[stacks 0E7Z]
theorem exists_flat_separated_finiteType_smoothing {k : Type u} [Field k]
    (X : SchemeOverField k) [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
    [IsLocalCompleteIntersectionOver k X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hns : {x : X.left | ¬ X.hom.SmoothAt x}.Finite) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of (PowerSeries k)))
      (_ : IsSeparated f) (_ : Scheme.Hom.FiniteType f) (_ : Flat f)
      (e : Over.mk (pullback.snd f (Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff))) ≅ X),
      Smooth (f.fiberToSpecResidueField
        (genericPoint (Spec (CommRingCat.of (PowerSeries k))))) :=
  sorry

end AlgebraicGeometry.SchemeOverField
