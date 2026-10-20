/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ConnectedLocallyConstant
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u w

namespace CategoryTheory.Sheaf

/- Lemma 59.64.8: if `X` is a connected scheme and `F` is a locally constant sheaf of
`Λ`-modules on its small étale site, then one `Λ`-module `M` works as a constant model on an
étale covering of `X`. -/
@[stacks 09BF] #check
  (CategoryTheory.Sheaf.existsConstantModuleCover :
    ∀ (X : Scheme.{u}) [ConnectedSpace X]
      {Λ : Type w} [Ring Λ]
      [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
      [∀ U : X.Etale,
        HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))
      [Sheaf.IsLocallyConstant F],
      ∃ (M : ModuleCat.{w} Λ) (I : Type (u + 1)) (U : I → X.Etale),
        X.smallEtaleTopology.CoversTop U ∧
          ∀ i : I, Nonempty (F.over (U i) ≅
            (constantSheaf (X.smallEtaleTopology.over (U i)) (ModuleCat.{w} Λ)).obj M))

end CategoryTheory.Sheaf
