module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Functors

/-!
# Natural transformations between filtration-stage functors

The stage comparisons and stage-to-underlying inclusions are already natural transformations on
filtered objects.  This leaf maps those owners degreewise to arbitrary homological-complex shapes,
so downstream constructions can whisker and compose them without rebuilding naturality from their
components.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w

namespace CategoryTheory.HomologicalComplex.Filtered.Stage

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {ι : Type w} {c : ComplexShape ι}

/-- The natural comparison from the `q`-th stage complex to the `p`-th stage complex for
`p ≤ q`. -/
@[stacks 012C "natural transformation between filtered stages"]
abbrev comparisonNatTrans {p q : ℤ} (hpq : p ≤ q) :
    (functor (C := C) (c := c) q) ⟶ functor p :=
  NatTrans.mapHomologicalComplex (FilteredObject.Stage.mapOfLE hpq) c

/-- A component of the stage-comparison natural transformation is the canonical stage
comparison. -/
@[simp, stacks 012C "component of the filtered-stage comparison"]
theorem comparisonNatTrans_app {p q : ℤ} (hpq : p ≤ q)
    (K : HomologicalComplex (FilteredObject C) c) :
    (comparisonNatTrans (c := c) hpq).app K = comparison K hpq := rfl

/-- The stage-comparison natural transformation at a reflexive inequality is the identity. -/
@[simp, stacks 012C "identity natural transformation between filtered stages"]
theorem comparisonNatTrans_refl (p : ℤ) :
    comparisonNatTrans (C := C) (c := c) (le_refl p) = 𝟙 (functor p) := sorry

/-- Stage-comparison natural transformations compose according to transitivity of the filtration
order. -/
@[simp, stacks 012C "composition of natural transformations between filtered stages"]
theorem comparisonNatTrans_comp {p q r : ℤ} (hpq : p ≤ q) (hqr : q ≤ r) :
    comparisonNatTrans (C := C) (c := c) hqr ≫ comparisonNatTrans hpq =
      comparisonNatTrans (hpq.trans hqr) := sorry

/-- The natural inclusion of the `p`-th stage complex into the underlying complex. -/
@[stacks 012C "natural transformation from a filtered stage to the underlying complex"]
abbrev inclusionNatTrans (p : ℤ) :
    (functor (C := C) (c := c) p) ⟶ underlyingFunctor :=
  NatTrans.mapHomologicalComplex (FilteredObject.Stage.toForget p) c

/-- A component of the stage-inclusion natural transformation is the canonical inclusion. -/
@[simp, stacks 012C "component of the filtered-stage inclusion"]
theorem inclusionNatTrans_app (p : ℤ)
    (K : HomologicalComplex (FilteredObject C) c) :
    (inclusionNatTrans (c := c) p).app K = inclusion K p := rfl

/-- Comparing stages and then including into the underlying complex gives the later-stage
inclusion as an equality of natural transformations. -/
@[simp, stacks 012C "factorization of the filtered-stage inclusion natural transformation"]
theorem comparisonNatTrans_comp_inclusionNatTrans {p q : ℤ} (hpq : p ≤ q) :
    comparisonNatTrans (C := C) (c := c) hpq ≫ inclusionNatTrans p =
      inclusionNatTrans q := sorry

end CategoryTheory.HomologicalComplex.Filtered.Stage
