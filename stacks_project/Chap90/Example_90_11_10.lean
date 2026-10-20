/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.TangentSpace
import StacksCheckRecall

/-! # Tangent space of a predeformation functor on `C_Λ` -/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor.IsPredeformationFunctor

/- Example 90.11.10: since `ArtinianLocalAlgCat Λ k` contains `k[V]` for
finite-dimensional `k`-vector spaces `V`, Definition 90.11.9 applies with
`S = Λ`, `R = k`, `C = ArtinianLocalAlgCat Λ k`, and
`F : ArtinianLocalAlgCat Λ k ⥤ Type v` a predeformation functor. The tangent
space is `TF = F(k[ε])`. -/
@[stacks 06SR] #check (CategoryTheory.Functor.IsPredeformationFunctor.tangentSpace_def :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    [CategoryTheory.Functor.IsPredeformationFunctor F],
    CategoryTheory.Functor.IsPredeformationFunctor.tangentSpace F =
      F.obj (ArtinianLocalAlgCat.dualNumber Λ k))

end CategoryTheory.Functor.IsPredeformationFunctor
