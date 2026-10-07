module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of scheme-theoretic images

A commutative square of scheme morphisms induces a morphism between the canonical
scheme-theoretic images. Both the maps into the targets and the maps from the sources form
commutative squares.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

noncomputable section

variable {X1 X2 Y1 Y2 : Scheme}
variable {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2}
variable {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2}

namespace Scheme.Hom

/-- The map between scheme-theoretic images induced by a commutative square. -/
@[stacks 01R9]
noncomputable def imageMap
    (sq : CommSq gX f₁ f₂ gY) :
    image f₁ ⟶ image f₂ :=
  Scheme.IdealSheafData.subschemeMap f₁.ker f₂.ker gY (by
    rw [← Scheme.Hom.ker_comp, ← sq.w]
    exact Scheme.Hom.le_ker_comp gX f₂)

/-- The induced image map commutes with the closed immersions into the targets. -/
@[stacks 01R9]
theorem imageMap_commSq
    (sq : CommSq gX f₁ f₂ gY) :
    CommSq (imageMap sq) (imageι f₁) (imageι f₂) gY := by
  constructor
  exact Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The maps from the sources to their scheme-theoretic images form a commutative square. -/
@[stacks 01R9]
theorem toImage_imageMap_commSq
    (sq : CommSq gX f₁ f₂ gY) :
    CommSq gX (toImage f₁) (toImage f₂) (imageMap sq) := by
  constructor
  rw [← cancel_mono (imageι f₂)]
  simp only [Category.assoc, toImage_imageι, (imageMap_commSq sq).w]
  rw [← Category.assoc, toImage_imageι]
  exact sq.w

end Scheme.Hom

end

end AlgebraicGeometry
