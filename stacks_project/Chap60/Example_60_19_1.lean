/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.VertexModule
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

/- Example 60.19.1 (1) -/
@[stacks 07L7] #check
  (CategoryTheory.CosimplicialObject.VertexModule.homotopy :
    ∀ A : CategoryTheory.CosimplicialObject RingCat.{u},
      PresheafOfModules.CosimplicialHomotopy
        (CategoryTheory.CosimplicialObject.VertexModule.presheaf A)
        (𝟙 (CategoryTheory.CosimplicialObject.VertexModule.presheaf A))
        (0 : CategoryTheory.CosimplicialObject.VertexModule.presheaf A ⟶
          CategoryTheory.CosimplicialObject.VertexModule.presheaf A))

/- Example 60.19.1 (2) -/
@[stacks 07L7] #check
  (CategoryTheory.CosimplicialObject.VertexModule.homotopic_zero :
    ∀ A : CategoryTheory.CosimplicialObject RingCat.{u},
      Nonempty (PresheafOfModules.CosimplicialHomotopy
        (CategoryTheory.CosimplicialObject.VertexModule.presheaf A)
        (𝟙 (CategoryTheory.CosimplicialObject.VertexModule.presheaf A))
        (0 : CategoryTheory.CosimplicialObject.VertexModule.presheaf A ⟶
          CategoryTheory.CosimplicialObject.VertexModule.presheaf A)))
