/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ClosedCover
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 42.19.4: if two closed subschemes cover `X` set-theoretically, then for every
`k : ℤ` their signed intersection pushforward and sum of ambient pushforwards form an exact
sequence ending in zero. -/
@[stacks 0F94] #check (AlgebraicGeometry.ChowGroup.ClosedCover.exact :
  ∀ {S X : AlgebraicGeometry.Scheme.{u}} (p : X ⟶ S)
    [AlgebraicGeometry.UniversallyCatenary S]
    [AlgebraicGeometry.LocallyOfFiniteType p] (δ : S → ℤ)
    [IsDimensionFunction δ] (Z₁ Z₂ : X.IdealSheafData)
    (_ : Z₁.support ⊔ Z₂.support = ⊤) (k : ℤ),
      (AlgebraicGeometry.ChowGroup.ClosedCover.complex p δ Z₁ Z₂ k).Exact ∧
        Epi (AlgebraicGeometry.ChowGroup.ClosedCover.complex p δ Z₁ Z₂ k).g)
