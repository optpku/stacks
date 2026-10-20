/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.IntegralClosure
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local

/-!
# Base-field conditions on schemes over a field

This leaf collects the standard ways in which the base field of a scheme can
be recovered from global functions, its function field, or its closed-point
residue fields.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.BaseField

variable {k : Type u} [Field k]

namespace GlobalSections

/-- The base field has no new integral elements in the ring of global functions. -/
@[stacks 04L8 "integrally closed base field in global sections"]
def isIntegrallyClosed (X : SchemeOverField k) : Prop :=
  X.hom.baseFieldIntegralClosureAlg = ⊥

end GlobalSections

namespace FunctionField

/-- The base field is algebraically closed in the function field of a variety. -/
@[stacks 04L8 "algebraically closed base field in the function field"]
def isAlgebraicallyClosed
    (X : SchemeOverField k) [Variety X] : Prop :=
  ∀ z : SchemeOverField.functionFieldCommAlg X, IsAlgebraic k z →
    z ∈ Set.range (algebraMap k (SchemeOverField.functionFieldCommAlg X))

end FunctionField

/-- The structure morphism of a scheme over `k` admits a section from `Spec k`. -/
@[stacks 04L7 "rational point over the base field"]
def hasRationalPoint (X : SchemeOverField k) : Prop :=
  ∃ e : Spec (CommRingCat.of k) ⟶ X.left, e ≫ X.hom = 𝟙 (Spec (CommRingCat.of k))

namespace ClosedPointResidues

/-- Every field extension of the base field that embeds over the base field into every
closed-point residue field is equal to the base field. -/
@[stacks 04L8 "closed-point residue fields intersect in the base field"]
def intersection_eq_base (X : SchemeOverField k) : Prop :=
  ∀ (K : CommAlgOverField k) (_ : IsField K),
    (∀ x : closedPoints X.left,
      Nonempty (K →ₐ[k] X.left.residueField x.1)) →
    Function.Surjective (algebraMap k K)

/-- The closed-point residue-field intersection condition is equivalently the assertion that
every common field subextension of the closed-point residue fields is the base field. -/
theorem intersection_eq_base_iff (X : SchemeOverField k) :
    intersection_eq_base X ↔
      ∀ (K : CommAlgOverField k) (_ : IsField K),
        (∀ x : closedPoints X.left,
          Nonempty (K →ₐ[k] X.left.residueField x.1)) →
        Function.Surjective (algebraMap k K) := sorry

end ClosedPointResidues

end AlgebraicGeometry.SchemeOverField.BaseField
