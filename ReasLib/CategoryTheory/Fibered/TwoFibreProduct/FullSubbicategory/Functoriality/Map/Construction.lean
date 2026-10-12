/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Forget
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps of full-subbicategory two-fibre products

A cospan transformation induces the explicit pseudo-pullback map, bundled in the selected
full subbicategory.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]
variable {X₁ Y₁ S₁ X₂ Y₂ S₂ : P.FullSubbicategory}
variable {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
variable {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}

/-- A transformation of cospans induces the componentwise map of their explicit
two-fibre-product apices. -/
@[stacks 0040 "map of full-subbicategory two-fibre-products induced by a cospan transformation"]
noncomputable def map (psi : CospanTransform F₁ G₁ F₂ G₂) :
    apex F₁ G₁ ⟶ apex F₂ G₂ :=
  Bicategory.InducedBicategory.mkHom
    (BasedCategory.PseudoPullback.map (CospanTransform.forget psi))

/-- Forgetting an induced full-subbicategory map recovers the explicit based
pseudo-pullback map. -/
@[simp]
theorem map.hom (psi : CospanTransform F₁ G₁ F₂ G₂) :
    (map psi).hom =
      BasedCategory.PseudoPullback.map (CospanTransform.forget psi) := sorry

end TwoFibreProduct

end CategoryTheory
