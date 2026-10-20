/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Basis.Cover

/-!
# Cofinal systems of basis covers

This file defines refinement and cofinality for families of covers by basis opens.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]
variable {B : Set (Opens X)}

namespace BasisCover

variable {U : BasisOpen B}

/-- A basis cover `𝒱` refines `𝒰` when every member of `𝒱` factors through a member of `𝒰`. -/
def Refines (𝒱 𝒰 : BasisCover B U) : Prop :=
  ∃ α : 𝒱.ι → 𝒰.ι,
    ∀ i : 𝒱.ι, ∃ f : 𝒱.obj i ⟶ 𝒰.obj (α i), 𝒱.hom i = f ≫ 𝒰.hom (α i)

/-- A family `C(U)` of basis covers is cofinal when every basis cover of `U` is refined by a
member of `C(U)`. -/
def IsCofinalSystem (C : ∀ U : BasisOpen B, Set (BasisCover B U)) : Prop :=
  ∀ U : BasisOpen B, ∀ 𝒰 : BasisCover B U,
    ∃ 𝒱 : BasisCover B U, 𝒱 ∈ C U ∧ Refines 𝒱 𝒰

end BasisCover

namespace CategoryTheory.Presheaf

variable {B : Set (Opens X)}

/-- A cofinal system of basis covers suffices to test the explicit basis sheaf condition, once
chosen covers of the pairwise intersections are supplied for the members of the system. -/
theorem isBasisSheaf_iff_hasSheafCondition_on_cofinalSystem
    (F : (BasisOpen B)ᵒᵖ ⥤ Type v)
    (C : ∀ U : BasisOpen B, Set (BasisCover B U))
    (h_inter :
      ∀ ⦃U : BasisOpen B⦄ (cover : BasisCover B U), cover ∈ C U →
        BasisIntersectionCover B cover)
    (hB : Opens.IsBasis B) (h_cofinal : BasisCover.IsCofinalSystem C) :
    IsBasisSheaf F ↔
      ∀ ⦃U : BasisOpen B⦄ (cover : BasisCover B U), ∀ h_cover : cover ∈ C U,
        cover.HasSheafCondition F (h_inter cover h_cover) := sorry

/-- If actual intersections of basis opens remain in the basis, a cofinal system of covers tests
the basis sheaf condition by unique amalgamation of compatible families. -/
theorem isBasisSheaf_iff_uniqueGluing_on_cofinalCovers
    (hB : Opens.IsBasis B)
    (h_inter :
      ∀ (U U' U'' : BasisOpen B), U'.obj ≤ U.obj → U''.obj ≤ U.obj →
        (U'.obj ⊓ U''.obj) ∈ B)
    (C : ∀ U : BasisOpen B, Set (BasisCover B U))
    (h_cofinal : BasisCover.IsCofinalSystem C)
    (F : (BasisOpen B)ᵒᵖ ⥤ Type v) :
    IsBasisSheaf F ↔
      ∀ ⦃U : BasisOpen B⦄ (cover : BasisCover B U), cover ∈ C U →
        ∀ sections : FamilyOfElementsOnObjects F cover.obj,
          sections.IsCompatible →
            ∃! glued : F.obj (op U), ∀ i, F.map (cover.hom i).op glued = sections i := sorry

end CategoryTheory.Presheaf
