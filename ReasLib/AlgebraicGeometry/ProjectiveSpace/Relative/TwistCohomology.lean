/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BaseChange
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.TwistCohomology.Naturality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal

/-!
# Relative cohomology of twisting sheaves on projective space

This file defines the relative graded pieces and twisting sheaves on projective space over a
scheme, and describes their higher direct images under the structure morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.MonoidalClosed
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The monomial exponent vectors of total degree `d` in `n + 1` variables.  This type is empty
when `d` is negative. -/
def relativeDegreeIndex (n : ℕ) (d : ℤ) : Type u :=
  ULift.{u, 0} { e : Fin (n + 1) → ℕ // 0 ≤ d ∧ ∑ i, e i = d.toNat }

/-- The free module sheaf representing the degree-`d` part of the polynomial algebra in
`n + 1` variables over a scheme. -/
noncomputable def relativeGradedPiece (S : Scheme.{u}) (n : ℕ) (d : ℤ) : S.Modules :=
  (SheafOfModules.free (R := S.ringCatSheaf) (relativeDegreeIndex.{u} n d) : S.Modules)

/-- The degree-`d` twisting sheaf on projective `n`-space over a scheme, obtained by pulling
back the integral standard twisting sheaf along the canonical second projection. -/
noncomputable def relativeTwistingSheaf (S : Scheme.{u}) (n : ℕ) (d : ℤ) :
    (ProjectiveSpace n S).Modules :=
  (Scheme.Modules.pullback
      (pullback.snd (terminal.from S)
        (terminal.from (ProjectiveSpace.scheme (ULift.{u} ℤ) n)))).obj
    (twistingSheaf (ULift.{u} ℤ) n d)

/-- The internal dual of the complementary relative graded piece occurring in top-degree
cohomology of a twisting sheaf. -/
noncomputable def relativeTopCohomologyDual (S : Scheme.{u}) (n : ℕ) (d : ℤ) : S.Modules :=
  (ihom (relativeGradedPiece S n (-((n : ℤ) + 1) - d))).obj (𝟙_ (S.Modules))

/-- The higher direct images of a relative twisting sheaf are the corresponding graded piece
in the active degree-zero case, the internal dual of the complementary graded piece in the
active top-degree case, and zero outside these cases. -/
theorem relativeTwistingSheaf_higherDirectImage_cases
    (S : Scheme.{u}) (n : ℕ) (d : ℤ) :
    (0 ≤ d →
      IsIsomorphic
        (((Scheme.Modules.pushforward (toBase n S)).rightDerived 0).obj
          (relativeTwistingSheaf S n d))
        (relativeGradedPiece S n d)) ∧
    (d < 0 →
      IsIsomorphic
        (((Scheme.Modules.pushforward (toBase n S)).rightDerived n).obj
          (relativeTwistingSheaf S n d))
        (relativeTopCohomologyDual S n d)) ∧
    (∀ q : ℕ, ¬ (q = 0 ∧ 0 ≤ d) → ¬ (q = n ∧ d < 0) →
      IsZero
        (((Scheme.Modules.pushforward (toBase n S)).rightDerived q).obj
          (relativeTwistingSheaf S n d))) := sorry

/-- For a nonnegative twist, its degree-zero higher direct image is the corresponding relative
graded piece. -/
theorem relativeTwistingSheaf_higherDirectImage_zero_of_nonneg
    (S : Scheme.{u}) (n : ℕ) (d : ℤ) (hd : 0 ≤ d) :
    IsIsomorphic
      (((Scheme.Modules.pushforward (toBase n S)).rightDerived 0).obj
        (relativeTwistingSheaf S n d))
      (relativeGradedPiece S n d) :=
  (relativeTwistingSheaf_higherDirectImage_cases S n d).1 hd

/-- A higher direct image of a relative twisting sheaf vanishes outside the active degree-zero
and top-degree cases. -/
theorem relativeTwistingSheaf_higherDirectImage_isZero_of_not_cases
    (S : Scheme.{u}) (n q : ℕ) (d : ℤ)
    (h_zero : ¬ (q = 0 ∧ 0 ≤ d)) (h_top : ¬ (q = n ∧ d < 0)) :
    IsZero
      (((Scheme.Modules.pushforward (toBase n S)).rightDerived q).obj
        (relativeTwistingSheaf S n d)) :=
  (relativeTwistingSheaf_higherDirectImage_cases S n d).2.2 q h_zero h_top

/-- For a negative twist, its top-degree higher direct image is the internal dual of the
complementary relative graded piece. -/
theorem relativeTwistingSheaf_higherDirectImage_top_of_neg
    (S : Scheme.{u}) (n : ℕ) (d : ℤ) (hd : d < 0) :
    IsIsomorphic
      (((Scheme.Modules.pushforward (toBase n S)).rightDerived n).obj
        (relativeTwistingSheaf S n d))
      (relativeTopCohomologyDual S n d) :=
  (relativeTwistingSheaf_higherDirectImage_cases S n d).2.1 hd

end AlgebraicGeometry.ProjectiveSpace
