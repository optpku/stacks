/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
import StacksCheckRecall

universe u

/- Definition 51.4.2: For a finitely generated ideal `I` of a commutative ring `A`,
`Ideal.LocalCohomology.dimension I hI` is the least admissible integer `d ≥ -1`,
called the cohomological dimension of `I` in `A`. -/
@[stacks 0DX8] #check
  (Ideal.LocalCohomology.dimension : ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG → ℤ)
