/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.PthPowerKernel

open CategoryTheory
open AlgebraicGeometry

universe u

/- Remark 39.8.5 (1): The equation `X₀ ^ p + α * X₁ ^ p = 0` defines a closed
subgroup scheme of the two-dimensional additive group over `k`. -/
@[stacks 047Q] #check
  (AlgebraicGeometry.PthPowerKernel.closedSubgroup :
    ∀ (p : ℕ) [Fact p.Prime] {k : Type u} [CommRing k] [CharP k p] (α : k),
      Scheme.ClosedSubgroup
        (AlgebraicGeometry.PthPowerKernel.ambient : Over (Spec (CommRingCat.of.{u} k))))

/- The closed subgroup carries the concrete quotient-presentation inclusion. -/
#check
  (AlgebraicGeometry.PthPowerKernel.closedSubgroup_inclusion :
    ∀ (p : ℕ) [Fact p.Prime] {k : Type u} [CommRing k] [CharP k p] (α : k),
      HEq (AlgebraicGeometry.PthPowerKernel.closedSubgroup p α).inclusion
        (AlgebraicGeometry.PthPowerKernel.inclusion p α))

/- Remark 39.8.5 (2): If `k` is a field of characteristic `p` and `α` is not a
p-th power, the closed subgroup scheme is reduced. -/
@[stacks 047Q] #check
  (AlgebraicGeometry.PthPowerKernel.isReduced :
    ∀ (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
      (α : k), α ∉ Set.range (fun β : k ↦ β ^ p) →
        AlgebraicGeometry.IsReduced (AlgebraicGeometry.PthPowerKernel.scheme p α))

/- Remark 39.8.5 (3): If `k` is a field of characteristic `p` and `α` is not a
p-th power, the closed subgroup scheme is irreducible. -/
@[stacks 047Q] #check
  (AlgebraicGeometry.PthPowerKernel.irreducibleSpace :
    ∀ (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
      (α : k), α ∉ Set.range (fun β : k ↦ β ^ p) →
        IrreducibleSpace (AlgebraicGeometry.PthPowerKernel.scheme p α))

/- Remark 39.8.5 (4): If `k` is a field of characteristic `p` and `α` is not a
p-th power, the structure morphism of the closed subgroup scheme is not smooth. -/
@[stacks 047Q] #check
  (AlgebraicGeometry.PthPowerKernel.notSmooth :
    ∀ (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
      (α : k), α ∉ Set.range (fun β : k ↦ β ^ p) →
        ¬ AlgebraicGeometry.Smooth (AlgebraicGeometry.PthPowerKernel.toBase p α))

/- Remark 39.8.5 (5): If `k` is a field of characteristic `p` and `α` is not a
p-th power, the closed subgroup scheme is not normal. -/
@[stacks 047Q] #check
  (AlgebraicGeometry.PthPowerKernel.notNormal :
    ∀ (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
      (α : k), α ∉ Set.range (fun β : k ↦ β ^ p) →
        ¬ (AlgebraicGeometry.PthPowerKernel.scheme p α).isNormal)
