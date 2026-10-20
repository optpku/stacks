/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Representable
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry Limits ChosenBigFppfSite

/- Lemma 87.19.3: Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of formal algebraic spaces over `S`. If `f ≫ g : X ⟶ Z` is
representable by algebraic spaces, then `f : X ⟶ Y` is representable by
algebraic spaces. -/
@[stacks 0AQ0] #check
  (AlgebraicGeometry.ChosenBigFppfSite.representableByAlgebraicSpaces.of_comp :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z),
    representableByAlgebraicSpaces (f ≫ g) → representableByAlgebraicSpaces f)

