module

public import ReasLib.CategoryTheory.Filtration.Complex.Convergence
public import ReasLib.CategoryTheory.Filtration.Complex.Representatives
public import ReasLib.CategoryTheory.Filtration.Lattice

/-!
# Representative Criteria for Filtered-Complex Convergence

This file connects the intrinsic convergence predicates for a filtered complex with the concrete
cycle and boundary representatives used in spectral-sequence calculations.  The core convergence
owner remains `Filtration/Complex/Convergence`; this leaf is only the representative-level view.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace FilteredComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

section LimitRepresentatives

namespace Cohomology.Representative

/-- The eventual boundary representative in degree `n` and filtration index `p`. -/
@[stacks 012V "eventual cohomology boundary representative"]
noncomputable abbrev eventualBoundary (K : FilteredComplex C) (n p : ℤ)
    [CompleteLattice (Subobject ((K.X n).obj))] :
    Subobject ((K.X n).obj) :=
  (K.d (n - 1) n).eventualBoundaryRepresentative p

/-- The eventual cycle representative in degree `n` and filtration index `p`. -/
@[stacks 012V "eventual cohomology cycle representative"]
noncomputable abbrev eventualCycle (K : FilteredComplex C) (n p : ℤ)
    [CompleteLattice (Subobject ((K.X n).obj))] :
    Subobject ((K.X n).obj) :=
  (K.d n (n + 1)).eventualCycleRepresentative p

end Cohomology.Representative

/-- The representative criterion for weak convergence: eventual boundaries and cycles agree with
the intrinsic boundary and cycle representatives in every degree and filtration index. -/
@[stacks 012V "representative criterion for weak convergence"]
def Cohomology.Representative.IsWeak (K : FilteredComplex C)
    [∀ n : ℤ, CompleteLattice (Subobject ((K.X n).obj))] : Prop :=
  ∀ n p : ℤ,
    Cohomology.Representative.eventualBoundary K n p =
        Cohomology.Representative.boundary K n p ∧
      Cohomology.Representative.cycle K n p =
        Cohomology.Representative.eventualCycle K n p

namespace Cohomology.Representative.IsWeak

variable {K : FilteredComplex C}
variable [∀ n : ℤ, CompleteLattice (Subobject ((K.X n).obj))]

/-- Extract the eventual-boundary equality at one bidegree. -/
theorem eventualBoundary_eq (hK : Cohomology.Representative.IsWeak K) (n p : ℤ) :
    Cohomology.Representative.eventualBoundary K n p =
      Cohomology.Representative.boundary K n p := sorry

/-- Extract the eventual-cycle equality at one bidegree. -/
theorem cycle_eq (hK : Cohomology.Representative.IsWeak K) (n p : ℤ) :
    Cohomology.Representative.cycle K n p =
      Cohomology.Representative.eventualCycle K n p := sorry

/-- Build the weak-convergence criterion from its two pointwise equalities. -/
theorem of_equalities
    (hB : ∀ n p : ℤ, Cohomology.Representative.eventualBoundary K n p =
      Cohomology.Representative.boundary K n p)
    (hZ : ∀ n p : ℤ, Cohomology.Representative.cycle K n p =
      Cohomology.Representative.eventualCycle K n p) :
    Cohomology.Representative.IsWeak K := sorry

/-- For an associated spectral sequence, the representative equalities give weak convergence to
the cohomology of the filtered complex.  The converse is deliberately not asserted: an abstract
isomorphism of quotient objects need not identify their ambient subobjects. -/
@[stacks 012V "weak convergence from representative equalities"]
theorem convergence
    (E : CohomologicalSpectralSequence C 0)
    (hAssoc : FilteredComplex.IsAssociated K E)
    (hK : Cohomology.Representative.IsWeak K) :
    Cohomology.Convergence.IsWeak K E := sorry

end Cohomology.Representative.IsWeak

end LimitRepresentatives

section CompleteSubobjects

/-- The representative criterion saying that the induced cohomology filtration is separated and
exhaustive in every degree. -/
@[stacks 012V "representative criterion for the induced cohomology filtration"]
def Cohomology.Representative.IsSeparatedExhaustive (K : FilteredComplex C)
    [∀ n : ℤ, CompleteLattice (Subobject ((K.X n).obj))] : Prop :=
  ∀ n : ℤ,
    Order.Filtration.Subquotient.IsSeparatedExhaustive (K.X n).filtration
      (imageSubobject ((K.d (n - 1) n).hom)) (kernelSubobject ((K.d n (n + 1)).hom))

namespace Cohomology.Representative.IsSeparatedExhaustive

variable {K : FilteredComplex C}
variable [∀ n : ℤ, CompleteLattice (Subobject ((K.X n).obj))]

/-- The representative criterion is equivalent to separatedness and exhaustiveness of every
induced cohomology filtration. -/
@[stacks 012V]
theorem iff_filtration :
    Cohomology.Representative.IsSeparatedExhaustive K ↔
      Cohomology.Filtration.IsSeparatedExhaustive K := sorry

end Cohomology.Representative.IsSeparatedExhaustive

end CompleteSubobjects

section LimitRepresentatives

namespace Cohomology.Representative.IsWeak

variable {K : FilteredComplex C}
variable [∀ n : ℤ, CompleteLattice (Subobject ((K.X n).obj))]

/-- For an associated spectral sequence, the weak representative criterion together with the
filtration representative criterion gives abutment.  The reverse implication would require a
canonical comparison compatible with ambient subobjects, not merely an abstract page isomorphism. -/
@[stacks 012V "abutment from representative criteria"]
theorem abuts
    (E : CohomologicalSpectralSequence C 0)
    (hAssoc : FilteredComplex.IsAssociated K E)
    (hweak : Cohomology.Representative.IsWeak K)
    (hfiltration : Cohomology.Representative.IsSeparatedExhaustive K) :
    Cohomology.Convergence.Abuts K E := sorry

end Cohomology.Representative.IsWeak

end LimitRepresentatives

end FilteredComplex
end CategoryTheory
