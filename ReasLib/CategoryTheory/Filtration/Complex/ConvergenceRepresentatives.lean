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

variable [LocallySmall.{v} C] [WellPowered.{v} C]

namespace Cohomology.Representative

/-- The eventual boundary representative in degree `n` and filtration index `p`. -/
@[stacks 012V "eventual cohomology boundary representative"]
noncomputable abbrev eventualBoundary (K : FilteredComplex C) (n p : ℤ)
    [HasCoproducts.{v} C] :
    Subobject ((K.X n).obj) :=
  (K.d (n - 1) n).eventualBoundaryRepresentative p

/-- The eventual cycle representative in degree `n` and filtration index `p`. -/
@[stacks 012V "eventual cohomology cycle representative"]
noncomputable abbrev eventualCycle (K : FilteredComplex C) (n p : ℤ)
    [HasWidePullbacks.{v} C] :
    Subobject ((K.X n).obj) :=
  (K.d n (n + 1)).eventualCycleRepresentative p

end Cohomology.Representative

variable [HasWidePullbacks.{v} C] [HasCoproducts.{v} C]

/-- Complete subobject lattices in every degree give the canonical eventual representatives of
a filtered complex, built from the infima and suprema of the finite-page representatives. -/
@[stacks 012Q "canonical eventual representatives of a filtered complex"]
noncomputable def Cohomology.Convergence.LimitRepresentatives.canonical (K : FilteredComplex C) :
    Cohomology.Convergence.LimitRepresentatives K where
  boundary n := FilteredObject.Hom.LimitRepresentatives.canonical (K.d (n - 1) n)
  cycle n := FilteredObject.Hom.LimitRepresentatives.canonical (K.d n (n + 1))

/-- The boundary representatives of the canonical package are the eventual boundaries. -/
@[simp, stacks 012Q "canonical eventual boundary of a filtered complex"]
theorem Cohomology.Convergence.LimitRepresentatives.canonical_boundary (K : FilteredComplex C)
    (n p : ℤ) :
    ((Cohomology.Convergence.LimitRepresentatives.canonical K).boundary n).boundary p =
      Cohomology.Representative.eventualBoundary K n p := sorry

/-- The cycle representatives of the canonical package are the eventual cycles. -/
@[simp, stacks 012Q "canonical eventual cycle of a filtered complex"]
theorem Cohomology.Convergence.LimitRepresentatives.canonical_cycle (K : FilteredComplex C)
    (n p : ℤ) :
    ((Cohomology.Convergence.LimitRepresentatives.canonical K).cycle n).cycle p =
      Cohomology.Representative.eventualCycle K n p := sorry

/-- The representative criterion for weak convergence: eventual boundaries and cycles agree with
the intrinsic boundary and cycle representatives in every degree and filtration index. -/
@[stacks 012V "representative criterion for weak convergence"]
def Cohomology.Representative.IsWeak (K : FilteredComplex C) : Prop :=
  ∀ n p : ℤ,
    Cohomology.Representative.eventualBoundary K n p =
        Cohomology.Representative.boundary K n p ∧
      Cohomology.Representative.cycle K n p =
        Cohomology.Representative.eventualCycle K n p

namespace Cohomology.Representative.IsWeak

variable {K : FilteredComplex C}

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

/-- For an associated spectral sequence, weak convergence to the cohomology of the filtered
complex holds if and only if the canonical eventual boundary and cycle representatives agree with
the intrinsic ones: equality holds in (012T) and (012S) for all degrees and filtration indices. -/
@[stacks 012V "weak convergence iff the representative equalities hold"]
theorem convergence_iff
    (E : CohomologicalSpectralSequence C 0)
    (hAssoc : FilteredComplex.IsAssociated K E) :
    Cohomology.Convergence.IsWeak K E ↔ Cohomology.Representative.IsWeak K := sorry

/-- For an associated spectral sequence, the representative equalities give weak convergence to
the cohomology of the filtered complex. -/
@[stacks 012V "weak convergence from representative equalities"]
theorem convergence
    (E : CohomologicalSpectralSequence C 0)
    (hAssoc : FilteredComplex.IsAssociated K E)
    (hK : Cohomology.Representative.IsWeak K) :
    Cohomology.Convergence.IsWeak K E := sorry

/-- Weak convergence along the canonical eventual representatives is the representative
criterion together with association. -/
@[stacks 012V "canonical weak convergence iff the representative equalities hold"]
theorem isWeakAlong_canonical_iff (E : CohomologicalSpectralSequence C 0) :
    Cohomology.Convergence.IsWeakAlong K E
        (Cohomology.Convergence.LimitRepresentatives.canonical K) ↔
      FilteredComplex.IsAssociated K E ∧ Cohomology.Representative.IsWeak K := sorry

end Cohomology.Representative.IsWeak

end LimitRepresentatives

section CompleteSubobjects

variable [LocallySmall.{v} C] [WellPowered.{v} C]
  [HasWidePullbacks.{v} C] [HasCoproducts.{v} C]

/-- The representative criterion saying that the induced cohomology filtration is separated and
exhaustive in every degree. -/
@[stacks 012V "representative criterion for the induced cohomology filtration"]
def Cohomology.Representative.IsSeparatedExhaustive (K : FilteredComplex C) : Prop :=
  ∀ n : ℤ,
    Order.Filtration.Subquotient.IsSeparatedExhaustive (K.X n).filtration
      (imageSubobject ((K.d (n - 1) n).hom)) (kernelSubobject ((K.d n (n + 1)).hom))

namespace Cohomology.Representative.IsSeparatedExhaustive

variable {K : FilteredComplex C}

/-- The representative criterion is equivalent to separatedness and exhaustiveness of every
induced cohomology filtration. -/
@[stacks 012V]
theorem iff_filtration :
    Cohomology.Representative.IsSeparatedExhaustive K ↔
      Cohomology.Filtration.IsSeparatedExhaustive K := sorry

end Cohomology.Representative.IsSeparatedExhaustive

end CompleteSubobjects

section LimitRepresentatives

variable [LocallySmall.{v} C] [WellPowered.{v} C]
  [HasWidePullbacks.{v} C] [HasCoproducts.{v} C]

namespace Cohomology.Representative.IsWeak

variable {K : FilteredComplex C}

/-- For an associated spectral sequence, abutment holds if and only if the weak representative
criterion and the filtration representative criterion hold. -/
@[stacks 012V "abutment iff the representative criteria hold"]
theorem abuts_iff
    (E : CohomologicalSpectralSequence C 0)
    (hAssoc : FilteredComplex.IsAssociated K E) :
    Cohomology.Convergence.Abuts K E ↔
      Cohomology.Representative.IsWeak K ∧
        Cohomology.Representative.IsSeparatedExhaustive K := sorry

/-- For an associated spectral sequence, the weak representative criterion together with the
filtration representative criterion gives abutment. -/
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
