/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Coequalizer
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

/- Lemma 35.13.8: a morphism coequalized by two scheme morphisms is their coequalizer
when its base change is their coequalizer on every member of an fpqc covering family and
on every pairwise overlap. -/
@[stacks 0BMN] #check
  (AlgebraicGeometry.Scheme.FpqcCovering.isColimit_of_baseChange :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (a b : X ⟶ Y) (c : Y ⟶ Z)
      (h : a ≫ c = b ≫ c) (𝒰 : SemiRepresentableFamily.Over.{v} Z)
      (h𝒰 : AlgebraicGeometry.Scheme.FpqcCovering 𝒰.obj)
      (h_member : ∀ i : 𝒰.index,
        Nonempty (IsColimit ((Cofork.ofπ c h).baseChange (𝒰.obj i).hom)))
      (h_overlap : ∀ i j : 𝒰.index,
        Nonempty (IsColimit ((Cofork.ofπ c h).baseChange (𝒰.overlapMap i j)))),
      Nonempty (IsColimit (Cofork.ofπ c h)))
