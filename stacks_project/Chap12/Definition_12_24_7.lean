/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.Bounded
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {r₀ : ℤ} (E : CohomologicalSpectralSequence C r₀)

/- Definition 12.24.7 (1) [0BDU]: regularity of a cohomological spectral sequence. -/
@[stacks 0BDU]
#check (E.IsRegular : Prop)

/- Definition 12.24.7 (2) [0BDU]: coregularity of a cohomological spectral sequence. -/
@[stacks 0BDU]
#check (E.IsCoregular : Prop)

/- Definition 12.24.7 (3) [0BDU]: boundedness on initial-page antidiagonals. -/
@[stacks 0BDU]
#check (E.IsBounded : Prop)

/- Definition 12.24.7 (4) [0BDU]: boundedness below. -/
@[stacks 0BDU]
#check (E.IsBoundedBelow : Prop)

/- Definition 12.24.7 (5) [0BDU]: boundedness above. -/
@[stacks 0BDU]
#check (E.IsBoundedAbove : Prop)
