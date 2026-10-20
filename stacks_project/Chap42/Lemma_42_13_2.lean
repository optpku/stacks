/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Topology.LocallyFinite
import stacks_project.Chap42.Situation_42_7_1

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 42.13.2: inverse images under a scheme morphism preserve locally finite
families of closed subsets for schemes locally of finite type over `S`. -/
@[stacks 02R9] #check (AlgebraicGeometry.Scheme.Hom.locallyFinite_preimage :
    ∀ {S X Y : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (pX : X ⟶ S) [LocallyOfFiniteType pX] (pY : Y ⟶ S) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) {I : Type v} (Z : I → Closeds Y)
    (hZ : LocallyFinite (fun i ↦ (Z i : Set Y))),
    LocallyFinite (fun i ↦ ((Z i).preimage f.continuous : Set X)))

end AlgebraicGeometry.Scheme.Hom
