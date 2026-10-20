/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Countability
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

/- Lemma 87.10.1: Let `S` be a scheme. Let `X` be an affine formal algebraic
space over `S`. The following are equivalent: there exists a sequential system
of thickenings of affine schemes over `S` whose sheaf colimit is isomorphic to
`X`, and there exists a directed affine thickening colimit presentation of `X`
as in Definition 87.9.1 whose index type `Λ` is countable. -/
@[stacks 0AII] #check
  (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.exists_natDirectedAffineThickeningColimit_iff :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X],
    (∃ D : ℕ ⥤ 𝒮.bigAffineSite S, IsNatDirectedAffineThickeningColimit D X) ↔
      (∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
          (_ : Countable Λ) (D : Λ ⥤ 𝒮.bigAffineSite S),
        IsDirectedAffineThickeningColimit D X))
