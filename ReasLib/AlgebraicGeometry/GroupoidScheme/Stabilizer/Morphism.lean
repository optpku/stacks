/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer

/-!
# Morphisms of stabilizers of groupoid schemes

A morphism of groupoid schemes induces a morphism between the underlying schemes of their
stabilizers, compatible with the arrow and object projections.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A groupoid morphism sends stabilizer arrows and base points compatibly to the target
stabilizer pullback. -/
theorem Hom.stabilizerMap_condition {S : Scheme.{u}} {G H : GroupoidScheme S}
    (f : Hom G H) :
    (G.toPreRelation.stabilizerToArrows ≫ f.arrow) ≫ H.toPreRelation.hom =
      (G.toPreRelation.stabilizer.hom ≫ f.obj) ≫ diag H.U := sorry

/-- The morphism of stabilizer carriers induced by a morphism of groupoid schemes. -/
def Hom.stabilizerMap {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) :
    G.toPreRelation.stabilizer.left ⟶ H.toPreRelation.stabilizer.left :=
  pullback.lift (G.toPreRelation.stabilizerToArrows ≫ f.arrow)
    (G.toPreRelation.stabilizer.hom ≫ f.obj) (f.stabilizerMap_condition)

/-- The stabilizer map is compatible with the maps to the arrow schemes. -/
theorem Hom.stabilizerMap_toArrows {S : Scheme.{u}} {G H : GroupoidScheme S}
    (f : Hom G H) :
    f.stabilizerMap ≫ H.toPreRelation.stabilizerToArrows =
      G.toPreRelation.stabilizerToArrows ≫ f.arrow := sorry

/-- The stabilizer map lies over the object component of the groupoid morphism. -/
theorem Hom.stabilizerMap_base {S : Scheme.{u}} {G H : GroupoidScheme S}
    (f : Hom G H) :
    f.stabilizerMap ≫ H.toPreRelation.stabilizer.hom =
      G.toPreRelation.stabilizer.hom ≫ f.obj := sorry

end AlgebraicGeometry.GroupoidScheme
