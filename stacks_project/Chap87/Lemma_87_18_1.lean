/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.ThickeningPresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.IsFormalAlgebraicSpace

universe u v

/- Lemma 87.18.1: A quasi-compact and quasi-separated formal algebraic space
is a nonempty directed colimit of algebraic spaces with thickening transitions. -/
@[stacks 0AJE] #check
  (AlgebraicGeometry.IsFormalAlgebraicSpace.exists_directedAlgebraicSpaceThickeningColimit :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsQuasiSeparatedFormalAlgebraicSpace X]
    [ChosenBigFppfSite.IsQuasiCompact (reduction X)],
    ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v))),
        IsDirectedAlgebraicSpaceThickeningColimit D X)
