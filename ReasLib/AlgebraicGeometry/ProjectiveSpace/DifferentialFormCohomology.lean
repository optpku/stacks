module

public import ReasLib.Algebra.Category.ModuleCat.FiniteFree.RankOne
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.EulerSequence
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.TwistCohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower

/-!
# Cohomology of differential forms on standard projective space

This file records the cohomology of exterior powers of the relative cotangent sheaf on standard
projective space, both without a twist and after a positive twist.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- On positive-dimensional standard projective space, the cohomology of the sheaf of relative
`p`-forms vanishes outside degree `p`, and also when `p` exceeds the dimension. -/
theorem projectiveSpaceDifferentialFormCohomology_isZero
    (A : Type u) [CommRing A] (n : ℕ) (hn : 1 ≤ n) (p q : ℕ)
    (hpq : ¬ (p = q ∧ q ≤ n)) :
    IsZero
      (Scheme.Hom.cohomology (ProjectiveSpace.toSpec A n)
        (Λ[p] Ω[(ProjectiveSpace.toSpec A n).toShHom]) q) := sorry

/-- In degrees `p` not exceeding the dimension, the `p`th cohomology of the sheaf of relative
`p`-forms on positive-dimensional standard projective space is free of rank one. -/
theorem projectiveSpaceDifferentialFormCohomology_freeRankOne
    (A : Type u) [CommRing A] (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p ≤ n) :
    CategoryTheory.ModuleCat.freeRankOne A
      (Scheme.Hom.cohomology (ProjectiveSpace.toSpec A n)
        (Λ[p] Ω[(ProjectiveSpace.toSpec A n).toShHom]) p) := sorry

/-- Every positive-degree cohomology module of a positive twist of the sheaf of relative
`p`-forms on positive-dimensional standard projective space vanishes. -/
theorem projectiveSpaceTwistedDifferentialFormCohomology_isZero
    (A : Type u) [CommRing A] (n : ℕ) (hn : 1 ≤ n) (p q : ℕ) (k : ℤ)
    (hq : 0 < q) (hk : 0 < k) :
    IsZero
      (Scheme.Hom.cohomology (ProjectiveSpace.toSpec A n)
        (ProjectiveSpace.twist A n
          (Λ[p] Ω[(ProjectiveSpace.toSpec A n).toShHom]) k) q) := sorry

end AlgebraicGeometry
