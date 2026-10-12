/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AffineConic
public import ReasLib.AlgebraicGeometry.Scheme.CubicNoSection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

/- Remark 111.34.4 (1): Exercise 111.34.3 is a special case of Tsen's theorem.
The conic defined by `A + B * x ^ 2 + C * y ^ 2`, with all three coefficients
nonzero, has a section over some nonempty open of Spec (Polynomial ℂ). -/
@[stacks 02F1]
#check (AlgebraicGeometry.AffineConicOverLine.exists_rational_section :
  ∀ (A B C : Polynomial ℂ), A ≠ 0 → B ≠ 0 → C ≠ 0 →
    ∃ U : AffineConicOverLine.base.Opens, Nonempty U ∧
      ∃ σ : U.toScheme ⟶ AffineConicOverLine.total A B C,
        σ ≫ AffineConicOverLine.toBase A B C = U.ι)

/- Remark 111.34.4 (2): Exercise 111.34.5 shows that the method is limited to
low-degree equations (conics when the base and fibre have dimension 1).
The displayed cubic `1 + t * x ^ 3 + t ^ 2 * y ^ 3` has no section over a
nonempty open of the base. This illustrates the limitation of the method,
not the failure of every higher-degree equation to admit a section. -/
@[stacks 02F1]
#check (AlgebraicGeometry.CubicNoSection.not_exists_nonempty_open_section :
  ¬ ∃ (U : CubicNoSection.base.Opens), Nonempty U ∧
    ∃ σ : U.toScheme ⟶ CubicNoSection.totalSpace, σ ≫ CubicNoSection.π = U.ι)
