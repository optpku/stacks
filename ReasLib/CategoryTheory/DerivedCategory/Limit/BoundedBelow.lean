module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.DerivedProduct
public import ReasLib.CategoryTheory.DerivedCategory.BoundedLocalization
public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Sequential Derived Limits of Bounded-Below Objects

This leaf owns the existence theorem for derived limits of sequential inverse
systems in a bounded-below derived category.  It is stated at the canonical
Mathlib owner `DerivedCategory.Plus`; the target is the ambient derived
category because a derived inverse limit need not remain bounded below.

The underlying construction uses bounded-below injective representatives,
K-injective products, and a Milnor triangle.  Those ingredients remain in
their respective lower-level leaves.
-/

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.DerivedCategory.Plus

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- Stacks 0BK7: a sequential inverse system of bounded-below derived objects
admits a derived inverse limit in the ambient derived category when the
underlying abelian category has countable products and enough injectives. -/
@[stacks 0BK7]
theorem exists_derivedLimit [HasCountableProducts 𝒜] [EnoughInjectives 𝒜]
    (K : SequentialInverseSystem (DerivedCategory.Plus 𝒜)) :
    ∃ L : DerivedCategory 𝒜,
      Nonempty (IsDerivedLimit (K ⋙ DerivedCategory.Plus.ι) L) := sorry

end CategoryTheory.DerivedCategory.Plus
