/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Affine

/-!
# Definition 87.9.1 affine compatibility bridge

The affine formal algebraic space API is owned by
`ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Affine`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

universe u v

namespace AlgebraicGeometry

/- Definition 87.9.1 affine colimit condition -/
#check (IsDirectedAffineThickeningColimit :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)

/- Definition 87.9.1 affine formal algebraic space condition -/
#check (IsAffineFormalAlgebraicSpace :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)

end AlgebraicGeometry
