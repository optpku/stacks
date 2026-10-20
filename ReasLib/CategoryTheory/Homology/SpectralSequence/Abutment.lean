module

public import ReasLib.CategoryTheory.Filtration.Exhaustive
public import ReasLib.CategoryTheory.Filtration.GradedPiece
public import ReasLib.CategoryTheory.Filtration.Complete
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Bounded
public import ReasLib.CategoryTheory.Homology.SpectralSequence.LimitStages

/-!
# Abutments of first-quadrant cohomological spectral sequences

This file records convergence to a graded target without choosing a filtered complex that
produces the spectral sequence.  An abutment consists of explicit limit stages and separated,
exhaustive filtrations whose graded pieces identify with the infinity page.
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory

open Limits

namespace CohomologicalSpectralSequenceNat.Page.One

variable {C : Type u} [Category.{v} C] [Abelian C] {r₀ : ℤ}

/-- Reindex a first-quadrant cohomological spectral sequence from its initial page as a spectral
sequence starting at page one. -/
abbrev ofInitial (E : CohomologicalSpectralSequenceNat C r₀) :
    SpectralSequence C
      (fun r ↦ ComplexShape.spectralSequenceNat
        ⟨r₀ + r - 1, 1 - (r₀ + r - 1)⟩) 1 where
  page r hr := E.page (r₀ + r - 1)
    (CohomologicalSpectralSequence.Page.One.le_reindexedPage r₀ r hr)
  iso r r' pq hrr' hr := E.iso (r₀ + r - 1) (r₀ + r' - 1) pq
    (CohomologicalSpectralSequence.Page.One.reindexedPage_succ r₀ hrr')
    (CohomologicalSpectralSequence.Page.One.le_reindexedPage r₀ r hr)

end CohomologicalSpectralSequenceNat.Page.One

namespace CohomologicalSpectralSequenceNat

variable {C : Type u} [Category.{v} C] [Abelian C] {r₀ : ℤ}

/-- A first-quadrant cohomological spectral sequence is regular when every outgoing differential
from every bidegree vanishes on all sufficiently late pages. -/
@[stacks 012U "regular first-quadrant spectral sequence"]
def IsRegular (E : CohomologicalSpectralSequenceNat C r₀) : Prop :=
  ∀ pq : ℕ × ℕ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), b ≤ r →
    ∀ pq' : ℕ × ℕ, (E.page r hr).d pq pq' = 0

/-- Every first-quadrant cohomological spectral sequence is regular: sufficiently late
differentials leave the first quadrant. -/
@[stacks 012U "regularity of first-quadrant spectral sequences"]
theorem isRegular (E : CohomologicalSpectralSequenceNat C r₀) :
    IsRegular E := sorry

/-- Abutment data for a first-quadrant cohomological spectral sequence, relative to fixed limit
stages and fixed filtrations on the total-degree targets.  The initial page `r₀` is arbitrary. -/
@[stacks 012U "first-quadrant abutment with explicit limit stages"]
def AbutsAlong
    (E : CohomologicalSpectralSequenceNat C r₀) (H : ℕ → C)
    (L : SpectralSequence.LimitStages (Page.One.ofInitial E))
    (F : ∀ n : ℕ, DecreasingFiltration (H n)) : Prop :=
  (∀ n : ℕ, IndexedFiltration.IsSeparated (F n)) ∧
    (∀ n : ℕ, IndexedFiltration.IsExhaustive (F n)) ∧
      (∀ n : ℕ, (F n).stage 0 = ⊤ ∧
        (F n).stage (Int.ofNat (n + 1)) = ⊥) ∧
        ∀ (n p : ℕ), p ≤ n →
          IsIsomorphic ((F n).gradedPiece (Int.ofNat p))
            (L.infinityPage (p, n - p))

/-- A first-quadrant cohomological spectral sequence with arbitrary initial page abuts to `H`
when it admits limit stages and separated, exhaustive filtrations supported in degrees `0` through
`n` and realizing its infinity page. -/
@[stacks 012U "first-quadrant abutment"]
def AbutsTo (E : CohomologicalSpectralSequenceNat C r₀) (H : ℕ → C) : Prop :=
  ∃ (L : SpectralSequence.LimitStages (Page.One.ofInitial E))
    (F : ∀ n : ℕ, DecreasingFiltration (H n)),
    AbutsAlong E H L F

namespace AbutsAlong

variable {E : CohomologicalSpectralSequenceNat C r₀} {H : ℕ → C}
variable {L : SpectralSequence.LimitStages (Page.One.ofInitial E)}
variable {F : ∀ n : ℕ, DecreasingFiltration (H n)}

/-- Every target filtration in an explicit first-quadrant abutment is separated. -/
theorem isSeparated (h : AbutsAlong E H L F) (n : ℕ) :
    IndexedFiltration.IsSeparated (F n) := sorry

/-- Every target filtration in an explicit first-quadrant abutment is exhaustive. -/
theorem isExhaustive (h : AbutsAlong E H L F) (n : ℕ) :
    IndexedFiltration.IsExhaustive (F n) := sorry

/-- The target filtration in an explicit first-quadrant abutment is supported in degrees
`0` through `n`.  These endpoint conditions force all graded pieces outside that range to
vanish, as required by the first-quadrant infinity page. -/
theorem stage_bounds (h : AbutsAlong E H L F) (n : ℕ) :
    (F n).stage 0 = ⊤ ∧
      (F n).stage (Int.ofNat (n + 1)) = ⊥ := h.2.2.1 n

/-- The degree-`p` graded piece in an explicit first-quadrant abutment is isomorphic to the
corresponding infinity-page entry. -/
theorem gradedPiece_isomorphic (h : AbutsAlong E H L F)
    (n p : ℕ) (hp : p ≤ n) :
    IsIsomorphic ((F n).gradedPiece (Int.ofNat p))
      (L.infinityPage (p, n - p)) := sorry

end AbutsAlong

namespace AbutsTo

variable {E : CohomologicalSpectralSequenceNat C r₀} {H H' : ℕ → C}

/-- An unqualified first-quadrant abutment supplies limit stages and filtrations satisfying
`AbutsAlong`. -/
theorem exists_along (h : AbutsTo E H) :
    ∃ (L : SpectralSequence.LimitStages (Page.One.ofInitial E))
      (F : ∀ n : ℕ, DecreasingFiltration (H n)),
      AbutsAlong E H L F := sorry

/-- Replacing every target by an isomorphic object does not change whether a first-quadrant
spectral sequence abuts to that target. -/
theorem congr_target (h : ∀ n : ℕ, IsIsomorphic (H n) (H' n)) :
    AbutsTo E H ↔ AbutsTo E H' := sorry

end AbutsTo

/-- Relative to explicit limit stages and target filtrations, a first-quadrant spectral sequence
converges when it is regular, abuts along those stages, and every target filtration is complete. -/
@[stacks 012U "first-quadrant convergence with explicit limit stages"]
def ConvergesAlong
    (E : CohomologicalSpectralSequenceNat C r₀) (H : ℕ → C)
    (L : SpectralSequence.LimitStages (Page.One.ofInitial E))
    (F : ∀ n : ℕ, DecreasingFiltration (H n)) : Prop :=
  E.IsRegular ∧ AbutsAlong E H L F ∧
    ∀ n : ℕ, DecreasingFiltration.IsComplete (F n)

/-- A first-quadrant cohomological spectral sequence converges to a graded target when it admits
explicit limit stages and complete target filtrations satisfying `ConvergesAlong`. -/
@[stacks 012U "first-quadrant convergence to a graded target"]
def ConvergesTo
    (E : CohomologicalSpectralSequenceNat C r₀) (H : ℕ → C) : Prop :=
  ∃ (L : SpectralSequence.LimitStages (Page.One.ofInitial E))
    (F : ∀ n : ℕ, DecreasingFiltration (H n)),
    ConvergesAlong E H L F

namespace ConvergesAlong

variable {E : CohomologicalSpectralSequenceNat C r₀} {H : ℕ → C}
variable {L : SpectralSequence.LimitStages (Page.One.ofInitial E)}
variable {F : ∀ n : ℕ, DecreasingFiltration (H n)}

/-- Convergence along explicit limit stages supplies regularity. -/
theorem isRegular (h : ConvergesAlong E H L F) : E.IsRegular := sorry

/-- Convergence along explicit limit stages supplies an abutment along the same stages and
filtrations. -/
theorem abuts (h : ConvergesAlong E H L F) : AbutsAlong E H L F := sorry

/-- Every target filtration in an explicit convergence datum is complete. -/
theorem isComplete (h : ConvergesAlong E H L F) (n : ℕ) :
    DecreasingFiltration.IsComplete (F n) := sorry

end ConvergesAlong

namespace ConvergesTo

variable {E : CohomologicalSpectralSequenceNat C r₀} {H H' : ℕ → C}

/-- Convergence to a graded target supplies explicit limit stages and target filtrations. -/
theorem exists_along (h : ConvergesTo E H) :
    ∃ (L : SpectralSequence.LimitStages (Page.One.ofInitial E))
      (F : ∀ n : ℕ, DecreasingFiltration (H n)),
      ConvergesAlong E H L F := sorry

/-- Convergence to a graded target supplies regularity of the spectral sequence. -/
theorem isRegular (h : ConvergesTo E H) : E.IsRegular := sorry

/-- Convergence to a graded target implies abutment to that target. -/
theorem abuts (h : ConvergesTo E H) : AbutsTo E H := sorry

/-- Replacing every target by an isomorphic object does not change convergence. -/
theorem congr_target (h : ∀ n : ℕ, IsIsomorphic (H n) (H' n)) :
    ConvergesTo E H ↔ ConvergesTo E H' := sorry

end ConvergesTo

end CohomologicalSpectralSequenceNat

namespace E₂CohomologicalSpectralSequenceNat

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The arbitrary-initial-page abutment predicate specialized to a spectral sequence starting
at `E₂`. -/
@[stacks 012U "first-quadrant abutment with explicit limit stages"]
abbrev AbutsAlong
    (E : E₂CohomologicalSpectralSequenceNat C) (H : ℕ → C)
    (L : SpectralSequence.LimitStages
      (CohomologicalSpectralSequenceNat.Page.One.ofInitial E))
    (F : ∀ n : ℕ, DecreasingFiltration (H n)) : Prop :=
  CohomologicalSpectralSequenceNat.AbutsAlong E H L F

/-- The arbitrary-initial-page abutment predicate specialized to a spectral sequence starting
at `E₂`. -/
@[stacks 012U "first-quadrant abutment"]
abbrev AbutsTo (E : E₂CohomologicalSpectralSequenceNat C) (H : ℕ → C) : Prop :=
  CohomologicalSpectralSequenceNat.AbutsTo E H

/-- Convergence with explicit limit stages, specialized to a first-quadrant spectral sequence
starting at `E₂`. -/
@[stacks 012U "first-quadrant convergence with explicit limit stages"]
abbrev ConvergesAlong
    (E : E₂CohomologicalSpectralSequenceNat C) (H : ℕ → C)
    (L : SpectralSequence.LimitStages
      (CohomologicalSpectralSequenceNat.Page.One.ofInitial E))
    (F : ∀ n : ℕ, DecreasingFiltration (H n)) : Prop :=
  CohomologicalSpectralSequenceNat.ConvergesAlong E H L F

/-- Convergence to a graded target, specialized to a first-quadrant spectral sequence starting
at `E₂`. -/
@[stacks 012U "first-quadrant convergence to a graded target"]
abbrev ConvergesTo
    (E : E₂CohomologicalSpectralSequenceNat C) (H : ℕ → C) : Prop :=
  CohomologicalSpectralSequenceNat.ConvergesTo E H

namespace AbutsAlong

variable {E : E₂CohomologicalSpectralSequenceNat C} {H : ℕ → C}
variable {L : SpectralSequence.LimitStages
  (CohomologicalSpectralSequenceNat.Page.One.ofInitial E)}
variable {F : ∀ n : ℕ, DecreasingFiltration (H n)}

/-- Every target filtration in an explicit abutment is separated. -/
theorem isSeparated (h : AbutsAlong E H L F) (n : ℕ) :
    IndexedFiltration.IsSeparated (F n) := sorry

/-- Every target filtration in an explicit abutment is exhaustive. -/
theorem isExhaustive (h : AbutsAlong E H L F) (n : ℕ) :
    IndexedFiltration.IsExhaustive (F n) := sorry

/-- The target filtration in an explicit first-quadrant abutment is supported in degrees
`0` through `n`. -/
theorem stage_bounds (h : AbutsAlong E H L F) (n : ℕ) :
    (F n).stage 0 = ⊤ ∧
      (F n).stage (Int.ofNat (n + 1)) = ⊥ :=
  CohomologicalSpectralSequenceNat.AbutsAlong.stage_bounds h n

/-- The degree-`p` graded piece of an explicit abutment is isomorphic to the corresponding
infinity-page entry. -/
theorem gradedPiece_isomorphic (h : AbutsAlong E H L F)
    (n p : ℕ) (hp : p ≤ n) :
    IsIsomorphic ((F n).gradedPiece (Int.ofNat p))
      (L.infinityPage (p, n - p)) := sorry

end AbutsAlong

namespace AbutsTo

variable {E : E₂CohomologicalSpectralSequenceNat C} {H : ℕ → C}

/-- An unqualified abutment supplies limit stages and filtrations satisfying `AbutsAlong`. -/
theorem exists_along (h : AbutsTo E H) :
    ∃ (L : SpectralSequence.LimitStages
        (CohomologicalSpectralSequenceNat.Page.One.ofInitial E))
      (F : ∀ n : ℕ, DecreasingFiltration (H n)),
      AbutsAlong E H L F := sorry

end AbutsTo

namespace ConvergesAlong

variable {E : E₂CohomologicalSpectralSequenceNat C} {H : ℕ → C}
variable {L : SpectralSequence.LimitStages
  (CohomologicalSpectralSequenceNat.Page.One.ofInitial E)}
variable {F : ∀ n : ℕ, DecreasingFiltration (H n)}

/-- Explicit convergence from `E₂` supplies regularity. -/
theorem isRegular (h : ConvergesAlong E H L F) : E.IsRegular := sorry

/-- Explicit convergence from `E₂` supplies abutment along the same data. -/
theorem abuts (h : ConvergesAlong E H L F) : AbutsAlong E H L F := sorry

/-- Every target filtration in an explicit convergence from `E₂` is complete. -/
theorem isComplete (h : ConvergesAlong E H L F) (n : ℕ) :
    DecreasingFiltration.IsComplete (F n) := sorry

end ConvergesAlong

namespace ConvergesTo

variable {E : E₂CohomologicalSpectralSequenceNat C} {H H' : ℕ → C}

/-- Convergence from `E₂` supplies explicit limit stages and target filtrations. -/
theorem exists_along (h : ConvergesTo E H) :
    ∃ (L : SpectralSequence.LimitStages
        (CohomologicalSpectralSequenceNat.Page.One.ofInitial E))
      (F : ∀ n : ℕ, DecreasingFiltration (H n)),
      ConvergesAlong E H L F := sorry

/-- Convergence from `E₂` supplies regularity. -/
theorem isRegular (h : ConvergesTo E H) : E.IsRegular := sorry

/-- Convergence from `E₂` implies abutment. -/
theorem abuts (h : ConvergesTo E H) : AbutsTo E H := sorry

/-- Convergence from `E₂` is invariant under degreewise isomorphism of targets. -/
theorem congr_target (h : ∀ n : ℕ, IsIsomorphic (H n) (H' n)) :
    ConvergesTo E H ↔ ConvergesTo E H' := sorry

end ConvergesTo

end E₂CohomologicalSpectralSequenceNat

end CategoryTheory
