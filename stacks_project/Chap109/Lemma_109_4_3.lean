/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Family
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

/- Lemma 109.4.3 -/
@[stacks 0E6F] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_etaleCovering_hProjective :
  ∀ {B : Scheme.{u}} {X : AlgebraicSpace B} {S : Over B}
    (f : X ⟶ AlgebraicSpace.ofOver S)
    [AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.IsFamily f],
    ∃ 𝒰 : S.left.Cover.{u} Scheme.etalePrecoverage,
      ∀ i, ∃ (Y : Scheme.{u}) (π : Y ⟶ 𝒰.X i)
        (e : pullback f (AlgebraicSpace.ofOverHomMk (𝒰.f i) rfl) ≅
          AlgebraicSpace.ofOver (Over.mk (π ≫ 𝒰.f i ≫ S.hom))),
        HProjective π ∧
          e.hom ≫ AlgebraicSpace.ofOverHomMk π rfl =
            pullback.snd f (AlgebraicSpace.ofOverHomMk (𝒰.f i) rfl))
