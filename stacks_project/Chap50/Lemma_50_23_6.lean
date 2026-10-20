/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

/- Lemma 50.23.6: the degree-`p` Gysin morphism is natural for a cartesian square of
finitely presented closed immersions whose rank-`c` locally free conormal sheaves are
identified by the canonical conormal comparison. -/
@[stacks 0G89] #check
  (@AlgebraicGeometry.Scheme.DeRham.Gysin.mapOfClosedImmersion_baseChange :
    ∀ {Z' X' S' Z X S : Scheme.{u}}
      (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (g : X' ⟶ X)
      (f' : X' ⟶ S') (f : X ⟶ S) (k : S' ⟶ S)
      [IsClosedImmersion i'] [IsClosedImmersion i]
      [FinitePresentation i'] [FinitePresentation i]
      (c p : ℕ)
      [SheafOfModules.IsFiniteLocallyFreeOfRank c (conormalSheaf i')]
      [SheafOfModules.IsFiniteLocallyFreeOfRank c (conormalSheaf i)]
      (sqZX : IsPullback h i' i g) (sqXS : CommSq g f' f k)
      [IsIso (Conormal.map sqZX.toCommSq)],
      CommSq
        ((Scheme.Modules.pullback g).map
          (AlgebraicGeometry.Scheme.DeRham.Gysin.mapOfClosedImmersion i f c p))
        (AlgebraicGeometry.Scheme.DeRham.Gysin.BaseChange.source
          h i' i g f' f k sqZX sqXS p)
        (AlgebraicGeometry.Scheme.DeRham.Gysin.BaseChange.target
          h i' i g f' f k c p sqZX sqXS)
        (AlgebraicGeometry.Scheme.DeRham.Gysin.mapOfClosedImmersion i' f' c p))
