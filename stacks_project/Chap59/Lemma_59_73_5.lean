/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.SetPresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace CategoryTheory.Sheaf

/- Lemma 59.73.5 -/
@[stacks 09Y9] #check (CategoryTheory.Sheaf.isConstructibleEtaleSet_iff_coequalizerPresentation :
  ∀ {X : Scheme.{u}},
    [CompactSpace X] → [QuasiSeparatedSpace X] →
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))] →
    [HasCoproducts.{u} (Sheaf X.smallEtaleTopology (Type (u + 1)))] →
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) →
      IsConstructibleEtaleSet
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteLocallyConstant G) F ↔
        IsCoequalizerOfQcQsSheafifiedRepresentable F)

end CategoryTheory.Sheaf
