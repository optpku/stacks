module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded Derived Categories — Notation and Characterization

@stack 0G1Y

Mathlib (v4.32.0) already defines the bounded derived categories as full subcategories of
`D(𝒜)` via the canonical t-structure:

* `DerivedCategory.Minus C` — bounded-above, via `t.minus.FullSubcategory`
* `DerivedCategory.Bounded C` — bounded, via `t.bounded.FullSubcategory`
* `DerivedCategory.Plus C` — bounded-below, via `t.plus.FullSubcategory`

This module adds:
1. Source-facing scoped notations: `D(A)`, `H⁽i⁾`, `D⁺(A)`, `D⁻(A)`, `Dᵇ(A)`.
2. Characterization theorems expressing membership in terms of cohomology vanishing.
3. A convenience functor restricting `H⁽i⁾` to `Dᵇ`.

## Notation

* `D(A)` — `DerivedCategory A`
* `H⁽i⁾` — `DerivedCategory.homologyFunctor _ i`
* `D⁺(A)` — `DerivedCategory.Plus A`
* `D⁻(A)` — `DerivedCategory.Minus A`
* `Dᵇ(A)` — `DerivedCategory.Bounded A`

## Main results

* `DerivedCategory.plus_iff` — `K ∈ D⁺` iff cohomology vanishes in low degrees.
* `DerivedCategory.minus_iff` — `K ∈ D⁻` iff cohomology vanishes in high degrees.
* `DerivedCategory.bounded_iff` — `K ∈ Dᵇ` iff cohomology vanishes in both extremes.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory
open DerivedCategory.TStructure

noncomputable section

universe w v u

namespace CategoryTheory

-- Notation layer on top of Mathlib's canonical owners.
scoped notation "D(" A:arg ")" => DerivedCategory A
/-- Scoped notation for the degree-`i` derived cohomology functor; compound indices use
parentheses, as in `H⁽(i + 1)⁾`. -/
scoped notation:max "H⁽" i:max "⁾" => DerivedCategory.homologyFunctor _ i
scoped notation "D⁺(" A:arg ")" => DerivedCategory.Plus A
scoped notation "D⁻(" A:arg ")" => DerivedCategory.Minus A
scoped notation "Dᵇ(" A:arg ")" => DerivedCategory.Bounded A

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

universe w'

variable [HasDerivedCategory.{w'} 𝒜]

namespace DerivedCategory

/-- A derived object is bounded above when it belongs to `D^{≤ n}` for some integer `n`. -/
@[stacks 0G1Y, stacks 0G20]
def IsBoundedAbove (K : DerivedCategory 𝒜) : Prop :=
  ∃ n : ℤ, K.IsLE n

/-- A derived object is bounded below when it belongs to `D^{≥ n}` for some integer `n`. -/
@[stacks 0G1Y, stacks 0G20]
def IsBoundedBelow (K : DerivedCategory 𝒜) : Prop :=
  ∃ n : ℤ, K.IsGE n

section Characterization

variable (K : D(𝒜))

/-- Membership in `t.plus` is equivalent to cohomology vanishing in sufficiently low
degrees. -/
theorem plus_iff :
    (t.plus : ObjectProperty (D(𝒜))) K ↔
      ∃ n : ℤ, ∀ i < n, IsZero ((H⁽i⁾).obj K) := by
  simp [Triangulated.TStructure.plus, isGE_iff]

/-- Membership in `t.minus` is equivalent to cohomology vanishing in sufficiently high
degrees. -/
theorem minus_iff :
    (t.minus : ObjectProperty (D(𝒜))) K ↔
      ∃ n : ℤ, ∀ i > n, IsZero ((H⁽i⁾).obj K) := by
  simp [Triangulated.TStructure.minus, isLE_iff]

/-- Membership in `t.bounded` is equivalent to cohomology vanishing in both extremes. -/
theorem bounded_iff :
    (t.bounded : ObjectProperty (D(𝒜))) K ↔
      (∃ a : ℤ, ∀ i < a, IsZero ((H⁽i⁾).obj K)) ∧
      (∃ b : ℤ, ∀ i > b, IsZero ((H⁽i⁾).obj K)) := by
  simp [Triangulated.TStructure.bounded, DerivedCategory.plus_iff, DerivedCategory.minus_iff]

end Characterization

end DerivedCategory

end CategoryTheory
