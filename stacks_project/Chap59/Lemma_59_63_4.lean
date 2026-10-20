/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.CharacteristicP
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 59.63.4: if `X` is separated and of finite type over an algebraically
closed field `k` of characteristic `p > 0`, then the constant `ZMod p` sheaf on
the small etale site has zero cohomology in every degree strictly above
`topologicalKrullDim X.left`, including when `X` is empty. -/
@[stacks 0A3N] #check
  (AlgebraicGeometry.Scheme.Etale.Small.constantZModCohomology_isZero_of_isAlgClosed :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (p q : ℕ) [CharP k p] [Fact (0 < p)]
      (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
      [IsSeparated X.hom]
      [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})],
      topologicalKrullDim X.left < (q : WithBot ℕ∞) →
        IsZero ((Sheaf.functorH X.left.smallEtaleTopology q).obj
          ((constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} (ZMod p))))))

end
