/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.NonMcQuillan

/-!
# A representable morphism of affine formal algebraic spaces with McQuillan target
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 110.75.3: there exists a representable morphism `f : X ⟶ Y` of affine
formal algebraic spaces with `Y` McQuillan, but `X` not McQuillan. -/
@[stacks 0CBE] #check (AlgebraicGeometry.exists_representable_isMcQuillan_source_not :
    ∃ (𝒮 : ChosenBigFppfSite.{u, u+1}) (S : 𝒮.carrier)
      (_ : HasWeakSheafify (𝒮.bigTopology S) (Type (u+1)))
      (_ : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (u+1))))
      (X Y : Sheaf (𝒮.bigTopology S) (Type (u+1)))
      (_ : IsAffineFormalAlgebraicSpace X) (_ : IsMcQuillan Y) (f : X ⟶ Y),
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable f ∧
        ¬ IsMcQuillan X)

end AlgebraicGeometry
