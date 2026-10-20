/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Base

/-!
# Naturality of the canonical base projection

Morphisms of categories fibred in groupoids commute with their canonical projections to the
identity fibration up to a canonical invertible 2-cell.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory
open Bicategory
open scoped Bicategory

universe u v

namespace CategoryTheory.FiberedCategoryOver.Groupoids

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids.{u, v, max u v, v} C}

/-- The whiskered projection comparison of a 1-morphism lifts the identity on the base. -/
private theorem baseProjection.naturality.isHomLift (f : X ⟶ Y) (a : X.total) :
    Functor.IsHomLift (base C).p (𝟙 (X.p.obj a))
      ((Functor.isoWhiskerRight (commIso f) (baseSection C)).hom.app a) := sorry

/-- A 1-morphism of categories fibred in groupoids is compatible with the canonical projections
to the identity fibration. -/
noncomputable def baseProjection.naturality (f : X ⟶ Y) :
    f ≫ baseProjection Y ≅ baseProjection X :=
  BasedFunctorIso.lift
    (BasedNatIso.mkNatIso
      (Functor.isoWhiskerRight (commIso f) (baseSection C))
      (baseProjection.naturality.isHomLift f))

end CategoryTheory.FiberedCategoryOver.Groupoids
