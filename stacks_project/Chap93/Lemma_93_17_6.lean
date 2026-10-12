/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Projective flat smoothings of proper lci curves with isolated singularities
-/

@[expose]
public section

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- Lemma 93.17.6: Let `X` be a scheme over a field `k`. Assume `X` is proper over `k`,
`X` is a local complete intersection over `k`, `X` has dimension `≤ 1`, and
`X ⟶ Spec k` is smooth except at finitely many points. Then there exists a flat
projective morphism `Y ⟶ Spec (PowerSeries k)` (that is, `Spec k[[t]]`) whose
generic fibre is smooth and whose special fibre is isomorphic to `X` as a
`k`-scheme. Here the generic fibre is the fibre over
`genericPoint (Spec (PowerSeries k))`, and the special fibre is the pullback of
`Y` along `Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff)`. -/
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

end AlgebraicGeometry.SchemeOverField
