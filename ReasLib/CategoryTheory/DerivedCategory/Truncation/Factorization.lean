module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# One-Step Factorization Through Derived Truncations

This leaf isolates the single-step vanishing arguments used when a chain is
factored through successively smaller or larger truncations.  The hypotheses
are explicit propositions, so downstream users do not need to install
object-specific boundedness instances merely to invoke the API.
-/

open CategoryTheory
open DerivedCategory.TStructure

universe w v u

namespace CategoryTheory.DerivedCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [HasDerivedCategory.{w} 𝒜]

namespace Concentrated

/-- A morphism between objects concentrated in degree `n` is zero when its
degree-`n` homology map is zero. -/
@[stacks 08Q2 "homology detects morphisms between concentrated objects"]
theorem hom_eq_zero_of_homologyMap_eq_zero
    {X Y : DerivedCategory 𝒜} {n : ℤ}
    (hXGE : X.IsGE n) (hXLE : X.IsLE n)
    (hYGE : Y.IsGE n) (hYLE : Y.IsLE n)
    (f : X ⟶ Y)
    (hf : (DerivedCategory.homologyFunctor 𝒜 n).map f = 0) :
    f = 0 := sorry

end Concentrated

namespace TruncLE

/-- A morphism from an object in `D^{≤ n}` to an object concentrated in
degree `n` is zero when its degree-`n` homology map is zero. -/
@[stacks 08Q2 "homology detects maps to a concentrated object"]
theorem hom_eq_zero_of_homologyMap_eq_zero
    {X Z : DerivedCategory 𝒜} {n : ℤ}
    (hX : X.IsLE n) (hZGE : Z.IsGE n) (hZLE : Z.IsLE n)
    (f : X ⟶ Z)
    (hf : (DerivedCategory.homologyFunctor 𝒜 n).map f = 0) :
    f = 0 := sorry

/-- A morphism from an object in `D^{≤ n}` whose degree-`n` homology map
vanishes lifts through the next smaller lower truncation. -/
@[stacks 08Q2 "one-step lower truncation factorization"]
theorem exists_lift_of_homologyMap_eq_zero
    {X Y : DerivedCategory 𝒜} {n : ℤ}
    (f : X ⟶ Y) (hX : X.IsLE n)
    (hf : (DerivedCategory.homologyFunctor 𝒜 n).map f = 0) :
    ∃ g : X ⟶ (t.truncLE (n - 1)).obj Y,
      g ≫ (t.truncLEι (n - 1)).app Y = f := sorry

end TruncLE

namespace TruncGE

/-- A morphism from an object concentrated in degree `n` to an object in
`D^{≥ n}` is zero when its degree-`n` homology map is zero. -/
@[stacks 08Q2 "homology detects maps from a concentrated object"]
theorem hom_eq_zero_of_homologyMap_eq_zero
    {Z Y : DerivedCategory 𝒜} {n : ℤ}
    (hZGE : Z.IsGE n) (hZLE : Z.IsLE n) (hY : Y.IsGE n)
    (f : Z ⟶ Y)
    (hf : (DerivedCategory.homologyFunctor 𝒜 n).map f = 0) :
    f = 0 := sorry

/-- A morphism into an object in `D^{≥ n}` whose degree-`n` homology map
vanishes descends from the next larger upper truncation. -/
@[stacks 08Q2 "one-step upper truncation factorization"]
theorem exists_desc_of_homologyMap_eq_zero
    {X Y : DerivedCategory 𝒜} {n : ℤ}
    (f : X ⟶ Y) (hY : Y.IsGE n)
    (hf : (DerivedCategory.homologyFunctor 𝒜 n).map f = 0) :
    ∃ g : (t.truncGE (n + 1)).obj X ⟶ Y,
      (t.truncGEπ (n + 1)).app X ≫ g = f := sorry

end TruncGE

end CategoryTheory.DerivedCategory
