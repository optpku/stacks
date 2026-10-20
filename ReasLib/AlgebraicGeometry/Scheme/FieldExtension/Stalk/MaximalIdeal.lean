/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.Local
public import ReasLib.RingTheory.RingHom.Local.MaximalIdeal

/-!
# Maximal ideals of stalks under field extension

This file relates dimensions and reduced closed fibres to preservation of
maximal ideals by field-extension base-change stalk maps.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension.Stalk.Local

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]

/-- If the source and base-change stalks have equal Krull dimension and the canonical residue-field
tensor is reduced, then the field-extension stalk map carries the source maximal ideal onto the
base-change maximal ideal. The reducedness hypothesis holds, for example, if the source residue
field extension or the scalar field extension is separable. -/
@[stacks 0C50]
theorem toSourceMap_mapsMaximalIdeal_of_ringKrullDim_eq_of_isReduced
    (y : FieldExtension.baseChange k K f)
    (h_dim :
      ringKrullDim (X.presheaf.stalk (FieldExtension.toSource k K f y)) =
        ringKrullDim ((FieldExtension.baseChange k K f).presheaf.stalk y))
    (h_reduced : _root_.IsReduced (FieldExtension.Stalk.pointTensor k K f y)) :
    RingHom.MapsMaximalIdeal (FieldExtension.Stalk.toSourceMap k K f y).hom := sorry

end AlgebraicGeometry.FieldExtension.Stalk.Local
