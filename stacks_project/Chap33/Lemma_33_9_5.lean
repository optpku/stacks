/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Proper
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 33.9.5: for a proper geometrically reduced scheme `X` over a field `k`, the canonical
map `k → Γ(X, ⊤)` is bijective if and only if `X` is geometrically connected over `k`. -/
@[stacks 0FD2] #check
  (AlgebraicGeometry.Scheme.GlobalSections.map_bijective_iff_geometricallyConnected_of_geometricallyReduced :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [GeometricallyReduced f],
      Function.Bijective (Scheme.Hom.globalSectionsMap f) ↔ GeometricallyConnected f)
