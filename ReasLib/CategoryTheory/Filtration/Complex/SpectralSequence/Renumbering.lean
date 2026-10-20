module

public import ReasLib.CategoryTheory.Filtration.Complex.Convergence
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Realization
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.FromZero.Relation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Realization and Convergence After Spectral-Sequence Renumbering

The usual page-and-bidegree renumbering changes a sequence beginning at `E₁` into one beginning
at `E₂`. The predicates below retain the original sequence when it is known, and provide
existential convenience interfaces when only the renumbered sequence matters. They do not tie
renumbering to Ext or to a particular construction of the filtered complex.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.FilteredComplex.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A renumbered spectral sequence realizes `H` through `F` when its original sequence realizes
`H` and the displayed new sequence is its standard page-and-bidegree renumbering. -/
@[stacks 0G1Y, stacks 0G20]
def RealizesViaRenumbering (F : FilteredComplex C)
    (E : CohomologicalSpectralSequence C 0)
    (E' : E₂CohomologicalSpectralSequence C) (H : ℤ → C) : Prop :=
  Realizes F E H ∧ CohomologicalSpectralSequence.Renumber.IsFromZero E E'

namespace RealizesViaRenumbering

/-- A realization via renumbering supplies the realization carried by its original sequence. -/
@[stacks 0G1Y, stacks 0G20]
theorem realizes {F : FilteredComplex C}
    {E : CohomologicalSpectralSequence C 0}
    {E' : E₂CohomologicalSpectralSequence C} {H : ℤ → C}
    (h : RealizesViaRenumbering F E E' H) : Realizes F E H := sorry

/-- A realization via renumbering supplies the relation between its original and new
sequences. -/
@[stacks 0G1Y, stacks 0G20]
theorem renumbering {F : FilteredComplex C}
    {E : CohomologicalSpectralSequence C 0}
    {E' : E₂CohomologicalSpectralSequence C} {H : ℤ → C}
    (h : RealizesViaRenumbering F E E' H) :
    CohomologicalSpectralSequence.Renumber.IsFromZero E E' := sorry

/-- Assemble a realization via renumbering from its two independent components. -/
@[stacks 0G1Y, stacks 0G20]
theorem of {F : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    {E' : E₂CohomologicalSpectralSequence C} {H : ℤ → C}
    (hrealizes : Realizes F E H)
    (hrenumber : CohomologicalSpectralSequence.Renumber.IsFromZero E E') :
    RealizesViaRenumbering F E E' H := sorry

end RealizesViaRenumbering

end CategoryTheory.FilteredComplex.SpectralSequence

namespace CategoryTheory.FilteredComplex.Cohomology.Convergence

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Convergence via renumbering retains the convergent original sequence together with the
renumbering relation to the displayed new sequence. -/
@[stacks 0G1Y, stacks 0G20]
def ConvergesViaRenumbering (K : FilteredComplex C)
    (E : CohomologicalSpectralSequence C 0)
    (E' : E₂CohomologicalSpectralSequence C) : Prop :=
  Converges K E ∧ CohomologicalSpectralSequence.Renumber.IsFromZero E E'

namespace ConvergesViaRenumbering

/-- Convergence via renumbering supplies convergence of the retained original sequence. -/
@[stacks 0G1Y, stacks 0G20]
theorem converges {K : FilteredComplex C}
    {E : CohomologicalSpectralSequence C 0}
    {E' : E₂CohomologicalSpectralSequence C}
    (h : ConvergesViaRenumbering K E E') : Converges K E := sorry

/-- Convergence via renumbering supplies the relation between its original and new sequences. -/
@[stacks 0G1Y, stacks 0G20]
theorem renumbering {K : FilteredComplex C}
    {E : CohomologicalSpectralSequence C 0}
    {E' : E₂CohomologicalSpectralSequence C}
    (h : ConvergesViaRenumbering K E E') :
    CohomologicalSpectralSequence.Renumber.IsFromZero E E' := sorry

/-- Assemble convergence via renumbering from convergence and the renumbering relation. -/
@[stacks 0G1Y, stacks 0G20]
theorem of {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    {E' : E₂CohomologicalSpectralSequence C} (hE : Converges K E)
    (hrenumber : CohomologicalSpectralSequence.Renumber.IsFromZero E E') :
    ConvergesViaRenumbering K E E' := sorry

end ConvergesViaRenumbering

/-- An `E₂`-spectral sequence converges after renumbering when it is the standard renumbering of
a convergent `E₀`-spectral sequence attached to the same filtered complex. -/
@[stacks 0G1Y, stacks 0G20]
def ConvergesAfterRenumbering (K : FilteredComplex C)
    (E' : E₂CohomologicalSpectralSequence C) : Prop :=
  ∃ E : CohomologicalSpectralSequence C 0,
    ConvergesViaRenumbering K E E'

namespace ConvergesAfterRenumbering

/-- Build convergence after renumbering from a convergent original sequence and the renumbering
relation. -/
@[stacks 0G1Y, stacks 0G20]
theorem of {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    {E' : E₂CohomologicalSpectralSequence C} (hE : Converges K E)
    (hrenumber : CohomologicalSpectralSequence.Renumber.IsFromZero E E') :
    ConvergesAfterRenumbering K E' := sorry

/-- Convergence after renumbering supplies an original sequence while retaining the conjunction
of convergence and renumbering as a named reusable predicate. -/
@[stacks 0G1Y, stacks 0G20]
theorem existsViaRenumbering {K : FilteredComplex C}
    {E' : E₂CohomologicalSpectralSequence C}
    (h : ConvergesAfterRenumbering K E') :
    ∃ E : CohomologicalSpectralSequence C 0,
      ConvergesViaRenumbering K E E' := sorry

/-- Convergence after renumbering supplies a convergent original sequence together with its
renumbering relation. -/
@[stacks 0G1Y, stacks 0G20]
theorem existsOriginal {K : FilteredComplex C}
    {E' : E₂CohomologicalSpectralSequence C}
    (h : ConvergesAfterRenumbering K E') :
    ∃ E : CohomologicalSpectralSequence C 0,
      Converges K E ∧
        CohomologicalSpectralSequence.Renumber.IsFromZero E E' := sorry

end ConvergesAfterRenumbering

end CategoryTheory.FilteredComplex.Cohomology.Convergence
