/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties

/-!
# Standard projective space as a variety

This file records the projective-variety and smooth-variety structures on standard projective
space over a field, together with its topological Krull dimension.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- Standard projective `n`-space over a field is a projective variety. -/
instance schemeOver_projectiveVariety (k : Type u) [Field k] (n : ℕ) :
    ProjectiveVariety (schemeOver k n) := sorry

/-- Standard projective `n`-space over a field is a smooth variety. -/
instance schemeOver_smoothVariety (k : Type u) [Field k] (n : ℕ) :
    SmoothVariety (schemeOver k n) := sorry

/-- Standard projective `n`-space over a field has topological Krull dimension `n`. -/
theorem topologicalKrullDim_scheme_eq (k : Type u) [Field k] (n : ℕ) :
    topologicalKrullDim (scheme k n) = n := sorry

end AlgebraicGeometry.ProjectiveSpace
