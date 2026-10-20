module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection comparisons for full-subbicategory two-fibre-product maps

Comparison isomorphisms for both projections and their natural assembly over the hom functor.
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
variable {psi phi : CospanTransform F₁ G₁ F₂ G₂}

/-- The induced map commutes with the first projection up to the canonical invertible cell. -/
@[stacks 0040 "first projection comparison for a full-subbicategory two-fibre-product map"]
noncomputable def map.fstIso (psi : CospanTransform F₁ G₁ F₂ G₂) :
    map psi ≫ fst F₂ G₂ ≅ fst F₁ G₁ ≫ psi.left :=
  Bicategory.InducedBicategory.isoMk
    (BasedCategory.PseudoPullback.map.fstIso (CospanTransform.forget psi))

/-- Forgetting the forward first-projection comparison recovers the corresponding explicit
based pseudo-pullback cell. -/
@[simp]
theorem map.fstIso.hom (psi : CospanTransform F₁ G₁ F₂ G₂) :
    (map.fstIso psi).hom.hom =
      (BasedCategory.PseudoPullback.map.fstIso
        (CospanTransform.forget psi)).hom := sorry

/-- Forgetting the inverse first-projection comparison recovers the inverse explicit based
pseudo-pullback cell. -/
@[simp]
theorem map.fstIso.inv (psi : CospanTransform F₁ G₁ F₂ G₂) :
    (map.fstIso psi).inv.hom =
      (BasedCategory.PseudoPullback.map.fstIso
        (CospanTransform.forget psi)).inv := sorry

/-- The induced map commutes with the second projection up to the canonical invertible cell. -/
@[stacks 0040 "second projection comparison for a full-subbicategory two-fibre-product map"]
noncomputable def map.sndIso (psi : CospanTransform F₁ G₁ F₂ G₂) :
    map psi ≫ snd F₂ G₂ ≅ snd F₁ G₁ ≫ psi.right :=
  InducedBicategory.isoMk
    (PseudoPullback.map.sndIso (CospanTransform.forget psi))

/-- Forgetting the forward second-projection comparison recovers the corresponding explicit
based pseudo-pullback cell. -/
@[simp]
theorem map.sndIso.hom (psi : CospanTransform F₁ G₁ F₂ G₂) :
    (map.sndIso psi).hom.hom =
      (BasedCategory.PseudoPullback.map.sndIso
        (CospanTransform.forget psi)).hom := sorry

/-- Forgetting the inverse second-projection comparison recovers the inverse explicit based
pseudo-pullback cell. -/
@[simp]
theorem map.sndIso.inv (psi : CospanTransform F₁ G₁ F₂ G₂) :
    (map.sndIso psi).inv.hom =
      (BasedCategory.PseudoPullback.map.sndIso
        (CospanTransform.forget psi)).inv := sorry

/-- The first projection comparison is `2`-natural in modifications of cospan
transformations. -/
theorem map₂.fstCommutes
    (Gamma : Pseudofunctor.StrongTrans.Hom psi phi) :
    map₂ Gamma ▷ CategoryTheory.TwoFibreProduct.fst F₂ G₂ ≫ (map.fstIso phi).hom =
      (map.fstIso psi).hom ≫
        CategoryTheory.TwoFibreProduct.fst F₁ G₁ ◁ CospanTransform.Hom.left Gamma := sorry

/-- The second projection comparison is `2`-natural in modifications of cospan
transformations. -/
theorem map₂.sndCommutes
    (Gamma : Pseudofunctor.StrongTrans.Hom psi phi) :
    map₂ Gamma ▷ CategoryTheory.TwoFibreProduct.snd F₂ G₂ ≫ (map.sndIso phi).hom =
      (map.sndIso psi).hom ≫
        CategoryTheory.TwoFibreProduct.snd F₁ G₁ ◁ CospanTransform.Hom.right Gamma := sorry

/-- The first-projection comparisons, natural in full-subbicategory cospan transformations. -/
@[stacks 0040 "natural first-projection comparison for full-subbicategory two-fibre-products"]
noncomputable def map.fstNatIso :
    mapFunctor ⋙ Bicategory.postcomp (apex F₁ G₁) (fst F₂ G₂) ≅
      CospanTransform.leftFunctor ⋙ Bicategory.precomp X₂ (fst F₁ G₁) :=
  NatIso.ofComponents map.fstIso map₂.fstCommutes

/-- The forward component of `map.fstNatIso` is the canonical first-projection comparison. -/
@[simp]
theorem map.fstNatIso.hom.app (psi : CospanTransform F₁ G₁ F₂ G₂) :
    map.fstNatIso.hom.app psi = (map.fstIso psi).hom := sorry

/-- The inverse component of `map.fstNatIso` is the inverse first-projection comparison. -/
@[simp]
theorem map.fstNatIso.inv.app (psi : CospanTransform F₁ G₁ F₂ G₂) :
    map.fstNatIso.inv.app psi = (map.fstIso psi).inv := sorry

/-- The second-projection comparisons, natural in full-subbicategory cospan transformations. -/
@[stacks 0040 "natural second-projection comparison for full-subbicategory two-fibre-products"]
noncomputable def map.sndNatIso :
    mapFunctor ⋙ Bicategory.postcomp (apex F₁ G₁) (snd F₂ G₂) ≅
      CospanTransform.rightFunctor ⋙ Bicategory.precomp Y₂ (snd F₁ G₁) :=
  NatIso.ofComponents map.sndIso map₂.sndCommutes

/-- The forward component of `map.sndNatIso` is the canonical second-projection comparison. -/
@[simp]
theorem map.sndNatIso.hom.app (psi : CospanTransform F₁ G₁ F₂ G₂) :
    map.sndNatIso.hom.app psi = (map.sndIso psi).hom := sorry

/-- The inverse component of `map.sndNatIso` is the inverse second-projection comparison. -/
@[simp]
theorem map.sndNatIso.inv.app (psi : CospanTransform F₁ G₁ F₂ G₂) :
    map.sndNatIso.inv.app psi = (map.sndIso psi).inv := sorry

end TwoFibreProduct

end CategoryTheory
