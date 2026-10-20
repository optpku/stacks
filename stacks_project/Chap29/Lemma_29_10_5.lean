/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Radicial

@[expose] public section
open AlgebraicGeometry CategoryTheory

/-- Lemma 29.10.5: the composite of radicial scheme morphisms is radicial.
The canonical universally-injective composition instance supplies this fact
through the established radicial/universally-injective equivalence. -/
@[stacks 02V1]
theorem AlgebraicGeometry.radicial_comp {X Y Z : Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Radicial f] [Radicial g] :
    Radicial (f ≫ g) :=
  (radicial_iff_universallyInjective (f ≫ g)).mpr
    (universallyInjective_isStableUnderComposition.comp_mem f g
      ((radicial_iff_universallyInjective f).mp inferInstance)
      ((radicial_iff_universallyInjective g).mp inferInstance))

/- Universally injective scheme morphisms are also stable under composition. -/
#check AlgebraicGeometry.universallyInjective_isStableUnderComposition
