/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Fpqc
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Proposition 59.17.1: for a quasi-coherent module `F` on `S`, the presheaf
`f : T ⟶ S ↦ Γ(T, (Scheme.Modules.pullback f).obj F)` is an fpqc sheaf. -/
@[stacks 03OG]
#check
  (AlgebraicGeometry.Scheme.Modules.pullbackSectionsPresheaf_isSheaf_fpqc :
    ∀ (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent],
      Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
        (Scheme.Modules.pullbackSectionsPresheaf (𝟭 (Over S)) F).presheaf)
