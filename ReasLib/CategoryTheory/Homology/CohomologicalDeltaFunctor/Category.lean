/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor

/-!
# The category of cohomological delta functors

Morphisms are the existing degreewise natural transformations commuting with
connecting maps. Identity and composition are the corresponding existing operations.
The explicit `Hom` and `HomIso` interfaces remain available from the core module.
-/

@[expose] public section

universe vA uA vB uB

namespace CategoryTheory.CohomologicalDeltaFunctor

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]

/-- The canonical category uses the given degreewise morphisms and their actual composition. -/
instance category : Category (CohomologicalDeltaFunctor A B) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

end CategoryTheory.CohomologicalDeltaFunctor
