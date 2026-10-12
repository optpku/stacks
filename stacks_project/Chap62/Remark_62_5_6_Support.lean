/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

section

variable {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] (r : ℕ)

/- Remark 62.5.6 (Support): For a locally finite-type morphism `f : X ⟶ S`
and a family `α` of nonnegative-dimensional cycles on its fibres, the support is
`⋃ s : S, f.fiberι s '' AlgebraicCycle.geometricSupport (α.toAlgebraicCycle s)`.
The fibrewise geometric supports are those of Definition 42.8.3. Their union
in `X` need not be closed; no closedness assertion is made. -/
@[stacks 0H4U] #check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.support :
  AlgebraicGeometry.Scheme.Hom.CyclesOnFibers f (r : ℤ) → Set X)

end
