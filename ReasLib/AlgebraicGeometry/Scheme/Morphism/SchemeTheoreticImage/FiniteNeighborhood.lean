/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.FiniteNeighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Proper

/-!
# Finite neighborhoods of scheme-theoretic images

This file gives a criterion for a scheme-theoretic image to become finite over
an open neighborhood.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- If the image under a morphism of one fiber of a proper composite is finite, then the
canonical scheme-theoretic image is finite over some open neighborhood of the base point. -/
theorem exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S) (s : S)
    (hs : Set.Finite (h '' ((h ≫ g) ⁻¹' ({s} : Set S))))
    [IsProper (h ≫ g)] [IsSeparated g] [LocallyOfFiniteType g] :
    ∃ U : S.Opens, s ∈ U ∧ IsFinite ((h.imageι ≫ g) ∣_ U) := sorry

end AlgebraicGeometry.Scheme.Hom
