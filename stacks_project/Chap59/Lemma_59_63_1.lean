/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.CharacteristicP
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

/- Lemma 59.63.1 (1): for an affine scheme of characteristic `p`, the
constant `ZMod p` sheaf on the small etale site has zero cohomology in every
degree `q ≥ 2`. -/
@[stacks 0A3K] #check
  (AlgebraicGeometry.Scheme.Etale.Small.constantZModCohomology_isZero_of_isAffine :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (p q : ℕ) [Fact p.Prime]
      [S.IsCharP p] [IsAffine S]
      [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})],
      2 ≤ q →
        IsZero ((Sheaf.functorH S.smallEtaleTopology q).obj
          ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} (ZMod p))))))

/- Lemma 59.63.1 (2): for a quasi-compact and quasi-separated scheme of
dimension `d` and characteristic `p`, the constant `ZMod p` sheaf on the small
etale site has zero cohomology in every degree `q ≥ 2 + d`. -/
@[stacks 0A3K] #check
  (AlgebraicGeometry.Scheme.Etale.Small.constantZModCohomology_isZero_of_dimension :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (p d q : ℕ) [Fact p.Prime]
      [S.IsCharP p] [CompactSpace S] [QuasiSeparatedSpace S]
      [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})],
      topologicalKrullDim S = (d : WithBot ℕ∞) → 2 + d ≤ q →
        IsZero ((Sheaf.functorH S.smallEtaleTopology q).obj
          ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} (ZMod p))))))

end
