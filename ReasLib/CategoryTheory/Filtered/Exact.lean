module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import ReasLib.CategoryTheory.Filtered.Components
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact colimits over componentwise filtered categories

@stack 04B0

This file packages the passage from an explicit postcomposition condition to exact colimits of
abelian groups. The connected-component filteredness criterion remains available separately.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {I : Type u} [Category.{v} I] [Small.{v} I] [HasSpanCocones I]

/-- Lemma 10.8.10: span cocones and postcomposition equalizers imply that colimits of diagrams
of abelian groups are exact. -/
@[stacks 04B0 "exact abelian-group colimits"]
theorem hasExactColimitsOfShape_addCommGrp_of_postcomposition
    (hMap :
      ∀ ⦃X Y : I⦄ (f g : X ⟶ Y),
        ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    HasExactColimitsOfShape I AddCommGrpCat := sorry

end CategoryTheory
