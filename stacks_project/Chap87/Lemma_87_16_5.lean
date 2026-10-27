/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Morphism.Separation
import StacksCheckRecall

/-!
# Lemma 87.16.5

A morphism from a separated algebraic space to a formal algebraic space is
separated.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

universe u v

/- Lemma 87.16.5: Let `S` be a scheme and `X` a formal algebraic space over
`S`. Every morphism `U ⟶ X` from a separated algebraic space over `S` is
separated. -/
@[stacks 0APX] #check
  (AlgebraicGeometry.ChosenBigFppfSite.Separated.of_isSeparated :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
      [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
      [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
      {U X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
      [ChosenBigFppfSite.IsSeparated U] [IsFormalAlgebraicSpace X]
      (f : U ⟶ X), ChosenBigFppfSite.Separated f)
