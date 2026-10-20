module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.Bounded
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (E : CohomologicalSpectralSequence C 0)
variable (hBelow : E.IsBoundedBelow) (hAbove : E.IsBoundedAbove)
variable (hBounded : E.IsBounded)

/- Lemma 12.24.8 (1) [0BDV]: regularity is eventual stabilization of cycle pieces. -/
@[stacks 0BDV]
#check (CohomologicalSpectralSequence.IsRegular.iff_eventually_cycle_eq E :
  E.IsRegular ↔
    ∀ p q : ℤ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : (0 : ℤ) ≤ r), b ≤ r →
      E.cycle (p, q) r hr = E.cycle (p, q) (r + 1)
        (CohomologicalSpectralSequence.le_page_succ hr))

/- Lemma 12.24.8 (2) [0BDV]: coregularity is eventual stabilization of boundary pieces. -/
@[stacks 0BDV]
#check (CohomologicalSpectralSequence.IsCoregular.iff_eventually_boundary_eq E :
  E.IsCoregular ↔
    ∀ p q : ℤ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : (0 : ℤ) ≤ r), b ≤ r →
      E.boundary (p, q) r hr = E.boundary (p, q) (r + 1)
        (CohomologicalSpectralSequence.le_page_succ hr))

/- Lemma 12.24.8 (3) [0BDV]: boundedness is the conjunction of the two one-sided bounds. -/
@[stacks 0BDV]
#check (CohomologicalSpectralSequence.IsBounded.iff_below_and_above E :
  E.IsBounded ↔ E.IsBoundedBelow ∧ E.IsBoundedAbove)

/- Lemma 12.24.8 (4) [0BDV]: bounded below implies regular. -/
@[stacks 0BDV]
#check (hBelow.isRegular : E.IsRegular)

/- Lemma 12.24.8 (5) [0BDV]: bounded above implies coregular. -/
@[stacks 0BDV]
#check (hAbove.isCoregular : E.IsCoregular)

/- A bounded spectral sequence supplies both stabilization properties directly. -/
#check (hBounded.isBoundedBelow : E.IsBoundedBelow)
#check (hBounded.isBoundedAbove : E.IsBoundedAbove)
#check (hBounded.isRegular : E.IsRegular)
#check (hBounded.isCoregular : E.IsCoregular)
