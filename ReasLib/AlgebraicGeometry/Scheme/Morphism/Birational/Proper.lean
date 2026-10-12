/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IsomorphismLocus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Normal

/-!
# Isomorphism loci of proper birational morphisms

This file gives pointwise criteria for a point to belong to the isomorphism locus of a proper
birational morphism with reduced source.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- Every codimension-zero point of a Noetherian target belongs to the isomorphism locus of a
proper birational morphism with reduced source. -/
@[stacks 0BFP]
theorem mem_isomorphismLocus_of_coheight_eq_zero
    (f : Y ⟶ X) [IsNoetherian X] [IsBirational f] [IsProper f] [IsReduced Y]
    (x : X) (hx : Order.coheight x = 0) :
    x ∈ f.isomorphismLocus := sorry

/-- A normal point with finite point-set fiber belongs to the isomorphism locus of a proper
birational morphism from a reduced scheme to a Noetherian scheme. -/
@[stacks 0BFP]
theorem mem_isomorphismLocus_of_finite_preimage_singleton_of_isNormalAt
    (f : Y ⟶ X) [IsNoetherian X] [IsBirational f] [IsProper f] [IsReduced Y]
    (x : X) (hfin : Set.Finite ((fun y : Y ↦ f y) ⁻¹' ({x} : Set X)))
    (hx : X.isNormalAt x) :
    x ∈ f.isomorphismLocus := sorry

/-- A codimension-one point with discrete valuation stalk belongs to the isomorphism locus of a
proper birational morphism from a reduced scheme to a Noetherian scheme. -/
@[stacks 0BFP]
theorem mem_isomorphismLocus_of_coheight_eq_one_of_isDiscreteValuationRing
    (f : Y ⟶ X) [IsNoetherian X] [IsBirational f] [IsProper f] [IsReduced Y]
    (x : X) (hx : Order.coheight x = 1)
    [IsDomain (X.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    x ∈ f.isomorphismLocus := sorry

/-- A normal target point admitting a point above it where a proper birational morphism is
finite-type quasi-finite belongs to the morphism's isomorphism locus. -/
@[stacks 0BFP]
theorem mem_isomorphismLocus_of_exists_finiteTypeQuasiFiniteAt_of_isNormalAt
    (f : Y ⟶ X) [IsNoetherian X] [IsBirational f] [IsProper f] [IsReduced Y]
    (x : X) (hx : X.isNormalAt x)
    (hquasi : ∃ y : Y, f y = x ∧ FiniteType.QuasiFiniteAt f y) :
    x ∈ f.isomorphismLocus := sorry

end Scheme.Hom
end AlgebraicGeometry
