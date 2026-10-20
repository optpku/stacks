/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 29.14.5: let `P` be a property of ring maps. Assume `P` is local and stable under
composition. Then the composition of morphisms locally of type `P` is locally of type `P`. -/
@[stacks 01SV] #check (AlgebraicGeometry.locallyOfType_comp :
  ∀ (P : {R T : Type u} → [CommRing R] → [CommRing T] → (R →+* T) → Prop)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z},
    RingHom.PropertyIsLocal P → RingHom.StableUnderComposition P →
      LocallyOfType P f → LocallyOfType P g → LocallyOfType P (f ≫ g))
