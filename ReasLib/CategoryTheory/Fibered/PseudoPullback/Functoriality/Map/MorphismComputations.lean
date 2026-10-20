/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Map.Construction

/-!
# Morphism computations for explicit pseudo-pullback maps

Formulas for the common base and endpoint projections of a mapped pseudo-pullback morphism.
-/

@[expose] public section

open CategoryTheory
open BasedFunctor
open Functor.IsHomLift
open scoped Bicategory BasedFunctor

universe u v
universe uX₁ vX₁ uY₁ vY₁ uS₁ vS₁
universe uX₂ vX₂ uY₂ vY₂ uS₂ vS₂

namespace CategoryTheory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

variable {X₁ : BasedCategory.{vX₁, uX₁} C}
variable {Y₁ : BasedCategory.{vY₁, uY₁} C}
variable {S₁ : BasedCategory.{vS₁, uS₁} C}
variable {X₂ : BasedCategory.{vX₂, uX₂} C}
variable {Y₂ : BasedCategory.{vY₂, uY₂} C}
variable {S₂ : BasedCategory.{vS₂, uS₂} C}
variable {F₁ : X₁ ⥤ᵇ S₁} {G₁ : Y₁ ⥤ᵇ S₁}
variable {F₂ : X₂ ⥤ᵇ S₂} {G₂ : Y₂ ⥤ᵇ S₂}

/-- The induced pseudo-pullback map retains the common base morphism. -/
@[simp]
theorem map.hom.base
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    {P Q : (PseudoPullback F₁ G₁).obj} (φ : P ⟶ Q) :
    baseMap ((map ψ).map φ) = baseMap φ := sorry
/- Proof strategy: unfold the public `map` owner and read the common base-map projection of its
private `homMk` assembly. -/

/-- The first morphism projection of an induced pseudo-pullback map is obtained by the left
component functor. -/
@[simp]
theorem map.hom.fst
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    {P Q : (PseudoPullback F₁ G₁).obj} (φ : P ⟶ Q) :
    fstMap ((map ψ).map φ) = ψ.left.map (fstMap φ) := sorry
/- Proof strategy: unfold the public owner and read the first map projection of its private
`homMk` assembly. -/

/-- The second morphism projection of an induced pseudo-pullback map is obtained by the right
component functor. -/
@[simp]
theorem map.hom.snd
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    {P Q : (PseudoPullback F₁ G₁).obj} (φ : P ⟶ Q) :
    sndMap ((map ψ).map φ) = ψ.right.map (sndMap φ) := sorry
/- Proof strategy: unfold the public owner and read the second map projection of its private
`homMk` assembly. -/

end
end PseudoPullback

end BasedCategory

end CategoryTheory
