module

public import Mathlib.Topology.Sheaves.Sheafify
public import ReasLib.CategoryTheory.Functor.Algebraic.Basic

/-!
# Sheafification of algebraic-structure-valued presheaves

This module records the sheafification universal property available from an underlying
`Type`-valued functor, without requiring a separately installed `HasWeakSheafify` instance for
the coefficient category.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

noncomputable section

universe w v u

variable {C : Type u} [Category.{v} C]
variable (F : C ⥤ Type w) [IsAlgebraicStructure C F]
variable {X : TopCat.{w}} (ℱ : X.Presheaf C)

namespace TopCat.Presheaf

/- The installed canonical `C`-valued sheafification APIs require an additional
`HasWeakSheafify (Opens.grothendieckTopology X) C` instance.  The theorem below keeps the
resulting sheaf and unit map explicit, while using `TopCat.Presheaf.sheafify` and
`TopCat.Presheaf.toSheafify` as the canonical set-valued owners. -/

/-- A presheaf with values in a type of algebraic structure admits a sheafification
whose underlying presheaf of sets is the ordinary sheafification, and maps to sheaves factor
uniquely through it. -/
theorem existsSheafificationOfIsAlgebraicStructure :
    ∃ (ℱ' : X.Sheaf C) (η : ℱ ⟶ ℱ'.obj)
      (e : (TopCat.Presheaf.sheafify (ℱ ⋙ F)).presheaf ≅ ℱ'.obj ⋙ F),
      TopCat.Presheaf.toSheafify (ℱ ⋙ F) ≫ e.hom = Functor.whiskerRight η F ∧
        ∀ (𝒢 : X.Sheaf C) (φ : ℱ ⟶ 𝒢.obj),
          ∃! ψ : ℱ' ⟶ 𝒢, η ≫ ψ.hom = φ := sorry
/- Proof strategy: construct the algebraic operations on `TopCat.Presheaf.sheafify (ℱ ⋙ F)`
using the finite-limit and filtered-colimit hypotheses in `IsAlgebraicStructure C F`, following
`morphism_factors_through_of_range_subset_of_injective` and
`exists_commSq_of_composite_range_subset_of_injective`. Bundle these operations into `ℱ'`, take
`η` over `TopCat.Presheaf.toSheafify (ℱ ⋙ F)`, and obtain `e` from the resulting identification of
underlying presheaves. For `φ : ℱ ⟶ 𝒢.obj`, define the factor sectionwise from the set-valued
sheafification universal property; faithfulness of `F` gives naturality and uniqueness, while
preservation of limits by `F` verifies compatibility with the algebraic structure. -/

end TopCat.Presheaf
