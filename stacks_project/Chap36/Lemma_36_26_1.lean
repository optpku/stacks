/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.Criteria

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 36.26.1: for a cartesian square of schemes and a morphism from the derived
pullback of `K` to `K'`, pointwise cohomology base change is equivalent to the affine
comparison condition on every compatible affine chart and on one compatible affine cover. -/
@[stacks 0DJ8] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.cohomologyBaseChange_tfae_affine :
    ∀ {X' X S' S : AlgebraicGeometry.Scheme.{u}}
      (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
      (sq : IsPullback g' f' f g)
      (K : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X)
      (K' : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X')
      (α : (AlgebraicGeometry.Scheme.DerivedQCoh.pullback g').obj K ⟶ K'),
      let D :=
        AlgebraicGeometry.Scheme.DerivedQCoh.CohomologyBaseChangeModel.canonical
          g' f' f g sq
      List.TFAE
        [ ∀ (x' : X') (i : ℤ), IsIso (D.pointMap K K' α x' i)
        , ∀ c : AlgebraicGeometry.Scheme.DerivedQCoh.AffineBaseChangeChart g' f' f g,
            IsIso (D.affineComparison K K' α c).map
        , ∃ cover : X'.AffineOpenCover,
            ∀ j : cover.I₀,
              ∃ c : AlgebraicGeometry.Scheme.DerivedQCoh.AffineBaseChangeChart g' f' f g,
                (cover.f j).opensRange = (c.U' : X'.Opens) ∧
                  IsIso (D.affineComparison K K' α c).map ])

end
