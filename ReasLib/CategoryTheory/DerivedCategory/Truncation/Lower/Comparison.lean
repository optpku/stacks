/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Homology.Conservative
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Homology
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Tower.Cone
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived-Limit Comparisons for the Lower Truncation Tower

The data-bearing `Comparison` is a direct specialization of the neutral
`HomotopyLimit.Comparison` structure. Its proposition-valued companion
`Comparison.Exists` is the appropriate interface when downstream code
only needs the existence of compatible derived-limit data. Neither public
surface expands a chosen product presentation.
-/

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.DerivedCategory.Truncation.Lower

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- Stacks 0H72: concrete data of a compatible map from a derived object to a
derived limit of its lower derived-truncation tower. -/
@[stacks 0H72]
abbrev Comparison (K : DerivedCategory 𝒜) {L : DerivedCategory 𝒜}
    (c : K ⟶ L) : Type _ :=
  HomotopyLimit.Comparison (cone K) c

/-- Stacks 0H72: the proposition that a morphism is compatible with some
derived-limit presentation of the lower derived-truncation tower. -/
@[stacks 0H72]
def Comparison.Exists (K : DerivedCategory 𝒜) {L : DerivedCategory 𝒜}
    (c : K ⟶ L) : Prop :=
  Nonempty (Comparison K c)

namespace Comparison.Exists

/-- A compatible lower-truncation comparison ensures that its target is a
homotopy limit of the canonical lower derived-truncation tower. The concrete
presentation remains owned by `Comparison`. -/
@[stacks 0H72]
theorem isOf {K L : DerivedCategory 𝒜} {c : K ⟶ L}
    (hc : Comparison.Exists K c) :
    HomotopyLimit.IsOf (tower K) L := sorry

/-- Stacks 0H72: two compatible maps from the same derived object to derived
limits of its lower derived-truncation tower are simultaneously isomorphisms. -/
@[stacks 0H72]
theorem isIso_iff {K L L' : DerivedCategory 𝒜} {c : K ⟶ L} {c' : K ⟶ L'}
    (hc : Comparison.Exists K c) (hc' : Comparison.Exists K c') :
    IsIso c ↔ IsIso c' := sorry

end Comparison.Exists

end CategoryTheory.DerivedCategory.Truncation.Lower
