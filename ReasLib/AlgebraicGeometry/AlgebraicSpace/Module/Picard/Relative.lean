/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.SchemesOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Pullback

/-!
# The relative Picard functor of a morphism of algebraic spaces

The unsheafified functor sends a scheme `T` over `B` to `Pic(X_T)`, and
`picardFunctor` is its fppf sheafification on `(Sch/B)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.CohStack (SchemesOver fiber fiberMap)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The presheaf on schemes over `B` sending `T` to the Picard group of the fibre
`X_T = X ×_B T`. -/
def presheaf (f : X ⟶ B) : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1) where
  obj σ := (fiber f σ.unop).PicardGroup
  map h := TypeCat.ofHom (picardPullback (fiberMap f h.unop))
  map_id := sorry
  map_comp := sorry

/-- Evaluation of the relative Picard presheaf at a scheme over `B`. -/
theorem presheaf_obj (f : X ⟶ B) (σ : SchemesOver B) :
    (presheaf f).obj (op σ) = (fiber f σ).PicardGroup := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativePicard

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The relative Picard sheaf is the fppf sheafification of the presheaf sending
schemes over the base to the Picard groups of their fibers. -/
def picardFunctor (f : X ⟶ B) : Sheaf (SchemesOver.fppfTopology B) (Type (u + 1)) :=
  (presheafToSheaf (SchemesOver.fppfTopology B) (Type (u + 1))).obj
    (RelativePicard.presheaf f)

/-- The underlying presheaf of the relative Picard sheaf is the chosen fppf
sheafification of the relative Picard presheaf. -/
theorem picardFunctor_val (f : X ⟶ B) :
    (picardFunctor f).obj =
      CategoryTheory.sheafify (SchemesOver.fppfTopology B) (RelativePicard.presheaf f) := sorry

end AlgebraicGeometry.AlgebraicSpace
