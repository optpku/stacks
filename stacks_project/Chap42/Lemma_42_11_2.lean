/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact.LocallyFinite
import stacks_project.Chap42.Situation_42_7_1

@[expose] public section

open CategoryTheory TopologicalSpace Topology

universe u v

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 42.11.2: a quasi-compact morphism between schemes locally of finite type over
`S` sends a locally finite family of closed subsets to a locally finite family of
closures of their images. -/
@[stacks 02R2] #check
  (AlgebraicGeometry.Scheme.Hom.locallyFinite_closure_image :
    ∀ {S X Y : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (pX : X ⟶ S) [LocallyOfFiniteType pX] (pY : Y ⟶ S) [LocallyOfFiniteType pY]
      (f : X ⟶ Y) [QuasiCompact f] {I : Type v} (Z : I → Closeds X),
      LocallyFinite (fun i ↦ (Z i : Set X)) →
        LocallyFinite (fun i ↦ closure (f.base '' (Z i : Set X))))

end AlgebraicGeometry.Scheme.Hom
