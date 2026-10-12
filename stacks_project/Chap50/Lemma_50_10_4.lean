/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.Canonical
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 50.10.4 (1): for every form degree `p` and weight `n : ℤ`, the comparison
constructed from actual homogeneous generators and tautological multiplication, from the weight-zero
punctured-line-bundle forms twisted by `ℒ^{⊗ n}` to the weight-`n` punctured forms,
is an isomorphism. -/
@[stacks 0FUH] #check
  (AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.twistComparison_isIso :
    ∀ {S X : Scheme.{u}} (f : X ⟶ S) (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
    [Scheme.IsRelativeSpectrumOver P]
    (p : ℕ) (n : ℤ),
      IsIso
        (AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.twistComparison
          f ℒ P p n))

/- Lemma 50.10.4 (2): the comparison defined by actual homogeneous generators
from `Ωᵧ_[X/S]` to the weight-zero pushed-forward de Rham complex `Ωᵧ_[L/S, 0]` of
the total line bundle is an isomorphism. -/
@[stacks 0FUH] #check
  (AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.degreeZeroComparison_isIso :
    ∀ {S X : Scheme.{u}} (f : X ⟶ S) (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
    [Scheme.IsRelativeSpectrumOver P],
      IsIso
        (AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.degreeZeroComparison
          f ℒ P))

/- Lemma 50.10.4 (3): for `0 < n` and `p : ℕ`, the restriction comparison induced
by the actual punctured-open immersion from `Ωᵖ_[L/S, n]` to `Ωᵖ_[L⋆/S, n]` is an
isomorphism. -/
@[stacks 0FUH] #check
  (AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.positiveWeightComparison_isIso :
    ∀ {S X : Scheme.{u}} (f : X ⟶ S) (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
    [Scheme.IsRelativeSpectrumOver P]
    (p n : ℕ) [NeZero n],
      IsIso
        (AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.positiveWeightComparison
          f ℒ P p n))
