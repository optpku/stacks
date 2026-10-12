/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Properties

@[expose] public section

/-!
# Affine-local ring properties of schemes

This file provides the basic owner for a property of commutative rings that
holds on an affine neighbourhood of every point of a scheme.  Cover,
restriction, and affine-chart criteria belong in
`ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Locality`.
-/

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme

/-- Affine opens inherit point-membership notation from their underlying open
subsets.  This compatibility instance lets affine-neighbourhood statements
write `x ∈ U` when `U : X.affineOpens`. -/
instance instMembershipAffineOpens (X : Scheme.{u}) : Membership X X.affineOpens where
  mem U x := x ∈ (U : X.Opens)

/-- `X` has ring property `P` locally when every point lies
in an affine open neighbourhood whose ring of sections satisfies `P`. -/
@[stacks 01OQ]
class HasRingPropertyLocally (X : Scheme.{u}) (P : CommRingCat.{u} → Prop) : Prop where
  /-- Every point admits an affine open neighbourhood whose section ring has
  property `P`. -/
  out : ∀ x : X, ∃ U : X.affineOpens, x ∈ U ∧ P (Γ(X, U))

namespace HasRingPropertyLocally

/-- A scheme with ring property `P` locally has, at each point, an affine open
neighbourhood whose section ring satisfies `P`. -/
theorem exists_affineOpen (X : Scheme.{u}) (P : CommRingCat.{u} → Prop)
    [h : X.HasRingPropertyLocally P] (x : X) :
    ∃ U : X.affineOpens, x ∈ U ∧ P (Γ(X, U)) := sorry

end HasRingPropertyLocally

/-- Unfold `HasRingPropertyLocally` as the affine-open neighbourhood witness
condition on points. -/
theorem hasRingPropertyLocally_iff (X : Scheme.{u}) (P : CommRingCat.{u} → Prop) :
    X.HasRingPropertyLocally P ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ U ∧ P (Γ(X, U)) := sorry

end Scheme
end AlgebraicGeometry
