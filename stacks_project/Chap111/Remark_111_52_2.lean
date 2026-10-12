/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Picard
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.TwistCohomology
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

variable (k : Type u) [Field k]

/- Remark 111.52.2 (1): let `k` be a field and write `P^2_k` for
`scheme k 2 = Proj (grading k 2)`, i.e. `Proj(k[X_0, X_1, X_2])`. Every invertible
sheaf on `P^2_k` is isomorphic to `𝒪(n) = twistingSheaf k 2 n` for some `n : ℤ`. -/
@[stacks 02AX] #check
  (AlgebraicGeometry.ProjectiveSpace.existsIsoTwistingSheaf k 2 (Nat.zero_lt_succ 1) :
    ∀ (L : (AlgebraicGeometry.ProjectiveSpace.scheme k 2).Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible L],
      ∃ d : ℤ,
        CategoryTheory.IsIsomorphic L
          (AlgebraicGeometry.ProjectiveSpace.twistingSheaf k 2 d))

/- Remark 111.52.2 (2): global sections of `𝒪(n)` on `P^2_k` recover the degree-`n`
part of `k[X_0, X_1, X_2]`, including negative degrees. -/
@[stacks 02AX] #check
  (AlgebraicGeometry.ProjectiveSpace.twistingSheaf.cohomology_zero k 2
      (Nat.zero_lt_succ 1) :
    ∀ d : ℤ,
      CategoryTheory.IsIsomorphic
        (AlgebraicGeometry.Scheme.Hom.cohomology
          (AlgebraicGeometry.ProjectiveSpace.toSpec k 2)
          (AlgebraicGeometry.ProjectiveSpace.twistingSheaf k 2 d) 0)
        (ModuleCat.of k (AlgebraicGeometry.ProjectiveSpace.gradedPiece k 2 d)))

/- Remark 111.52.2 (3): for a quasi-coherent sheaf `F` on `P^2_k`, the twist
`F(n)` is definitionally tensoring `F` with the canonical twisting sheaf
`twistingSheaf k 2 n`. -/
@[stacks 02AX] #check
  (AlgebraicGeometry.ProjectiveSpace.twist k 2 :
    (AlgebraicGeometry.ProjectiveSpace.scheme k 2).Modules → ℤ →
      (AlgebraicGeometry.ProjectiveSpace.scheme k 2).Modules)

end AlgebraicGeometry.ProjectiveSpace
