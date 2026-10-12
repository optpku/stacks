/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowMotive.Factorization

@[expose] public section

open CategoryTheory CategoryTheory.Idempotents
open AlgebraicGeometry AlgebraicGeometry.Correspondence
open scoped CategoryTheory.MonoidalCategory

universe w v u

/- Lemma 45.4.8: a `ℚ`-linear strong symmetric monoidal functor on degree-zero
Chow correspondences whose `c₂`-image splits as a tensor-invertible object extends to
Chow motives, uniquely up to a unique compatible monoidal natural isomorphism. -/
@[stacks 0FGH]
#check (ChowMotive.ProjectiveLine.existsUniqueFactorization :
  ∀ {k : Type u} [Field k] {C : Type v} [Category.{w} C] [Preadditive C] [Linear ℚ C]
    [MonoidalCategory C] [SymmetricCategory C] [IsIdempotentComplete C]
    (F : Correspondence.Category k ⥤ C) [F.Braided] [F.Linear ℚ]
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1)
    (U : C) [MonoidalCategory.isInvertibleObject U]
    (r : Retract U (F.obj (Correspondence.ProjectiveLine.asObject k)))
    (h_c2 : let c₂ : Correspondence.ProjectiveLine.asObject k ⟶
        Correspondence.ProjectiveLine.asObject k :=
      Correspondence.ProjectiveLine.timesPoint x
      r.r ≫ r.i = F.map c₂),
    ∃ P : ChowMotive.Factorization k F, ∀ Q : ChowMotive.Factorization k F,
      ∃! e : P.lift ≅ Q.lift,
        (ChowMotive.restriction k C).mapIso e ≪≫ Q.comparison = P.comparison)
