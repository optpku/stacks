/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.OpenSubset
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

/- Lemma 29.32.3: for compatible opens `U ⊆ X` and `V ⊆ S`, restriction of
`Ω_{X/S}` to `U` is canonically isomorphic to `Ω_{U/V}`. -/
@[stacks 01US]
#check (AlgebraicGeometry.Scheme.RelativeDifferentials.OpenSubset.comparison_isIso :
  ∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V),
    IsIso (AlgebraicGeometry.Scheme.RelativeDifferentials.OpenSubset.comparison f U V hU))

#check @AlgebraicGeometry.Scheme.RelativeDifferentials.OpenSubset.comparison
#check @AlgebraicGeometry.Scheme.RelativeDifferentials.OpenSubset.comparison_spec
#check @AlgebraicGeometry.Scheme.RelativeDifferentials.OpenSubset.eq_comparison
