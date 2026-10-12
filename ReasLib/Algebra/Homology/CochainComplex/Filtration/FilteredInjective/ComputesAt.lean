/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Views
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.KInjective.Bounded
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Value.Explicit

/-!
# Pointwise Derived Computation by Filtered-Injective Views

The graded pieces, filtration stages, and underlying complexes of a bounded-below
filtered-injective complex have canonical termwise-injective presentations.  This module exposes
the corresponding pointwise right-derived computation facts as named theorems, without adding
overlapping instances to typeclass search.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

noncomputable section

universe v v' u u'

namespace CochainComplex.FilteredInjectivePlus

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D]

namespace GradedPiece

/-- The canonical termwise-injective presentation of a graded piece computes every pointwise
right-derived functor on bounded-below homotopy complexes. -/
@[stacks 05TH "pointwise derived computation by a filtered-injective graded piece"]
theorem computesAt (F : HomotopyCategory.Plus C ⥤ D) (p : ℤ)
    (I : CochainComplex.FilteredInjectivePlus C) :
    RightDerived.ComputesAt F (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.quotient C).obj ((functor C p).obj I)) := sorry

/-- The canonical value comparison for a graded-piece view, with its computation witness passed
explicitly rather than installed as a local instance. -/
@[stacks 05TH "pointwise derived value on a filtered-injective graded piece"]
noncomputable def valueIso (F : HomotopyCategory.Plus C ⥤ D) (p : ℤ)
    (I : CochainComplex.FilteredInjectivePlus C) :=
  RightDerived.ComputesAt.valueIsoOf F (HomotopyCategory.Plus.quasiIso C)
    ((HomotopyCategory.Plus.quotient C).obj ((functor C p).obj I)) (computesAt F p I)

end GradedPiece

namespace Stage

/-- The canonical termwise-injective presentation of a filtration stage computes every
pointwise right-derived functor on bounded-below homotopy complexes. -/
@[stacks 05TH "pointwise derived computation by a filtered-injective stage"]
theorem computesAt (F : HomotopyCategory.Plus C ⥤ D) (p : ℤ)
    (I : CochainComplex.FilteredInjectivePlus C) :
    RightDerived.ComputesAt F (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.quotient C).obj ((functor C p).obj I)) := sorry

/-- The canonical value comparison for a stage view, with its computation witness passed
explicitly rather than installed as a local instance. -/
@[stacks 05TH "pointwise derived value on a filtered-injective stage"]
noncomputable def valueIso (F : HomotopyCategory.Plus C ⥤ D) (p : ℤ)
    (I : CochainComplex.FilteredInjectivePlus C) :=
  RightDerived.ComputesAt.valueIsoOf F (HomotopyCategory.Plus.quasiIso C)
    ((HomotopyCategory.Plus.quotient C).obj ((functor C p).obj I)) (computesAt F p I)

end Stage

namespace Underlying

/-- The canonical termwise-injective presentation of the underlying complex computes every
pointwise right-derived functor on bounded-below homotopy complexes. -/
@[stacks 05TH "pointwise derived computation by an underlying filtered-injective complex"]
theorem computesAt (F : HomotopyCategory.Plus C ⥤ D)
    (I : CochainComplex.FilteredInjectivePlus C) :
    RightDerived.ComputesAt F (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.quotient C).obj ((functor C).obj I)) := sorry

/-- The canonical value comparison for an underlying view, with its computation witness passed
explicitly rather than installed as a local instance. -/
@[stacks 05TH "pointwise derived value on an underlying filtered-injective complex"]
noncomputable def valueIso (F : HomotopyCategory.Plus C ⥤ D)
    (I : CochainComplex.FilteredInjectivePlus C) :=
  RightDerived.ComputesAt.valueIsoOf F (HomotopyCategory.Plus.quasiIso C)
    ((HomotopyCategory.Plus.quotient C).obj ((functor C).obj I)) (computesAt F I)

end Underlying

end CochainComplex.FilteredInjectivePlus
