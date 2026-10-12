/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ConstantPullback

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An affine scheme admits an integral surjective cover whose closed subschemes
have vanishing positive-degree étale cohomology with finite constant coefficients. -/
theorem exists_integralSurjective_etaleHq_constantFinite_isZero
    {X : Scheme.{u}} [IsAffine X] :
    ∃ (X' : Scheme.{u}) (f : X' ⟶ X),
      IsIntegralHom f ∧ Surjective f ∧
        ∀ {Z' : Scheme.{u}} (i' : Z' ⟶ X') [IsClosedImmersion i']
          (M : AddCommGrpCat.{u}) [Finite M]
          (q : ℕ) (hq : 1 ≤ q),
          IsZero
            ((Sheaf.functorH Z'.smallEtaleTopology q).obj
              ((constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u}).obj M)) :=
  sorry

/-- Every positive-degree constant-coefficient étale cohomology class on a
closed subscheme is killed by a finite surjective finitely presented cover. -/
theorem exists_finiteFpSurjective_etaleHq_eq_zero
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    (M : AddCommGrpCat.{u}) [Finite M]
    (q : ℕ) (hq : 1 ≤ q)
    (ξ : (Sheaf.functorH Z.smallEtaleTopology q).obj
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M)) :
    ∃ (X' : Scheme.{u}) (f : X' ⟶ X),
      IsFinite f ∧ Surjective f ∧ FinitePresentation f ∧
        etaleHq_constant_pullback (pullback.snd f i) M q ξ = 0 :=
  sorry

end AlgebraicGeometry.Scheme.Hom
