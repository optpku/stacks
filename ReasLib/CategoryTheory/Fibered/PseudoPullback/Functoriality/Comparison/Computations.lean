/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Comparison.Identity
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Comparison.Composition

/-!
# Computation API for pseudo-pullback map coherence

This leaf supplies the component formulas for the packaged identity and composition comparison
isomorphisms. It is the narrow import for downstream simplification without re-reading the
coherence constructions themselves.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor

universe u v
universe uX₁ vX₁ uY₁ vY₁ uS₁ vS₁
universe uX₂ vX₂ uY₂ vY₂ uS₂ vS₂
universe uX₃ vX₃ uY₃ vY₃ uS₃ vS₃

namespace CategoryTheory

open Bicategory

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
variable {X₃ : BasedCategory.{vX₃, uX₃} C}
variable {Y₃ : BasedCategory.{vY₃, uY₃} C}
variable {S₃ : BasedCategory.{vS₃, uS₃} C}
variable {F₁ : X₁ ⥤ᵇ S₁} {G₁ : Y₁ ⥤ᵇ S₁}
variable {F₂ : X₂ ⥤ᵇ S₂} {G₂ : Y₂ ⥤ᵇ S₂}
variable {F₃ : X₃ ⥤ᵇ S₃} {G₃ : Y₃ ⥤ᵇ S₃}

/-- The forward component of the identity comparison is its explicit objectwise comparison. -/
@[simp]
theorem map.idIso.hom.app
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) (P : (PseudoPullback F G).obj) :
    (map.idIso F G).hom.toNatTrans.app P = (mapId.component F G P).hom := sorry

/-- The inverse component of the identity comparison is its explicit objectwise comparison. -/
@[simp]
theorem map.idIso.inv.app
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) (P : (PseudoPullback F G).obj) :
    (map.idIso F G).inv.toNatTrans.app P = (mapId.component F G P).inv := sorry

/-- The forward component of the composition comparison is its explicit objectwise comparison. -/
@[simp]
theorem map.compIso.hom.app
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    (P : (PseudoPullback F₁ G₁).obj) :
    (map.compIso ψ φ).hom.toNatTrans.app P = (mapComp.component ψ φ P).hom := sorry

/-- The inverse component of the composition comparison is its explicit objectwise comparison. -/
@[simp]
theorem map.compIso.inv.app
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    (P : (PseudoPullback F₁ G₁).obj) :
    (map.compIso ψ φ).inv.toNatTrans.app P = (mapComp.component ψ φ P).inv := sorry

end

end PseudoPullback

end BasedCategory

end CategoryTheory
