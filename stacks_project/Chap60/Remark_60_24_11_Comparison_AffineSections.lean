/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace CrystallineAffineSections

variable {Y : Scheme.{u}} (U : Y.affineOpens) (M : Y.Modules)

/-- The image of the whole affine spectrum is exactly its specified open,
so restriction identifies local sections without an arbitrary-open tensor law. -/
theorem chart_image_top : U.property.fromSpec ''ᵁ ⊤ = U.1 := by
  ext x
  change x ∈ U.property.fromSpec '' Set.univ ↔ x ∈ U.1
  rw [Set.image_univ, U.property.range_fromSpec]
  rfl

/-- Local sections on an affine open are canonically global sections of
the actual pullback to its spectrum. This uses restriction/pullback adjunction
and the chart's image equality, not an asserted bijection of arbitrary maps. -/
noncomputable def pullbackSectionsIso :
    (M.presheaf.obj (op U.1)) ≅
      (((Scheme.Modules.pullback U.property.fromSpec).obj M).presheaf.obj (op ⊤)) :=
  M.presheaf.mapIso (eqToIso (chart_image_top U)).op ≪≫
    (M.restrictAppIso U.property.fromSpec ⊤).symm ≪≫
      ((Scheme.Modules.toPresheaf _).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback U.property.fromSpec).app M)).app (op ⊤)

end CrystallineAffineSections
