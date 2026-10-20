/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Definition 29.14.2: A scheme morphism is locally of type `P` when every source point has
an affine open neighborhood mapping into an affine open of the target such that the induced
map on rings of sections satisfies `P`. -/
@[stacks 01SS] #check (AlgebraicGeometry.locallyOfType_iff :
  ∀ (P : {R S : Type u} → [CommRing R] → [CommRing S] → (R →+* S) → Prop)
      {X Y : Scheme.{u}} (f : X ⟶ Y),
    AlgebraicGeometry.LocallyOfType P f ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ V : Y.affineOpens,
          ∃ e : U ≤ f ⁻¹ᵁ V,
            P (CommRingCat.Hom.hom (f.appLE V U e)))
