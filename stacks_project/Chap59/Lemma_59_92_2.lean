/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CohomologicalDimension.ProperFiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom

universe u

/- Lemma 59.92.2: if `f : X ⟶ Y` is a proper morphism of schemes all of whose
scheme-theoretic fibres have dimension `≤ n`, then for any abelian torsion sheaf
`F` on `X` étale we have `higherDirectImage (smallEtalePullback f) F q = 0` for
`q > 2n`. The fibre bound is `∀ y, f.fiberDimension y ≤ n`, equivalently
`topologicalKrullDim (f.fiber y) ≤ n`. -/
@[stacks 095U] #check
  (AlgebraicGeometry.Scheme.Etale.higherDirectImage_isZero_of_isProper_fiberDimension_le :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      {n : ℕ} (hdim : ∀ y : Y, f.fiberDimension y ≤ (n : WithBot ℕ∞))
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (hF : IsLocallyTorsion F)
      {q : ℕ} (hq : 2 * n < q),
    IsZero (higherDirectImage (smallEtalePullback f) F q :
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))

end
