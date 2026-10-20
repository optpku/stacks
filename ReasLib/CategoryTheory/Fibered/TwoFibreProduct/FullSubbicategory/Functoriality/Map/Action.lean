/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.NatTrans
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-cell action on full-subbicategory two-fibre-product maps

Modifications of cospan transformations act on the induced maps. The component API reads the
result back in the explicit based pseudo-pullback.
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
variable {psi phi chi : CospanTransform F₁ G₁ F₂ G₂}

/-- A modification of cospan transformations induces the locally full `2`-morphism between
the corresponding explicit two-fibre-product maps. -/
@[stacks 0040 "modification action on full-subbicategory two-fibre-product maps"]
noncomputable def map₂
    (Gamma : Pseudofunctor.StrongTrans.Hom psi phi) :
    map psi ⟶ map phi :=
  Bicategory.InducedBicategory.mkHom₂
    (BasedCategory.PseudoPullback.map₂ (CospanModification.forget Gamma))

/-- Forgetting the induced `2`-morphism recovers the explicit based pseudo-pullback
`2`-morphism. -/
@[simp]
theorem map₂.hom
    (Gamma : Pseudofunctor.StrongTrans.Hom psi phi) :
    (map₂ Gamma).hom =
      BasedCategory.PseudoPullback.map₂ (CospanModification.forget Gamma) := sorry

/-- The base component of an induced two-fibre-product `2`-morphism is the identity. -/
@[simp]
theorem map₂.base
    (Gamma : Pseudofunctor.StrongTrans.Hom psi phi)
    (A : (BasedCategory.PseudoPullback F₁.hom G₁.hom).obj) :
    BasedCategory.PseudoPullback.baseMap ((map₂ Gamma).hom.toNatTrans.app A) =
      𝟙 (BasedCategory.PseudoPullback.baseObj A) := sorry

/-- The first component of an induced two-fibre-product `2`-morphism is the underlying left
component of the cospan modification. -/
@[simp]
theorem map₂.fst
    (Gamma : Pseudofunctor.StrongTrans.Hom psi phi)
    (A : (BasedCategory.PseudoPullback F₁.hom G₁.hom).obj) :
    BasedCategory.PseudoPullback.fstMap ((map₂ Gamma).hom.toNatTrans.app A) =
      (CospanTransform.Hom.left Gamma).hom.toNatTrans.app
        (BasedCategory.PseudoPullback.fstObj A) := sorry

/-- The second component of an induced two-fibre-product `2`-morphism is the underlying right
component of the cospan modification. -/
@[simp]
theorem map₂.snd
    (Gamma : Pseudofunctor.StrongTrans.Hom psi phi)
    (A : (BasedCategory.PseudoPullback F₁.hom G₁.hom).obj) :
    BasedCategory.PseudoPullback.sndMap ((map₂ Gamma).hom.toNatTrans.app A) =
      (CospanTransform.Hom.right Gamma).hom.toNatTrans.app
        (BasedCategory.PseudoPullback.sndObj A) := sorry

/-- The full-subbicategory two-fibre-product action preserves identity cospan modifications. -/
@[simp]
theorem map₂.id (psi : CospanTransform F₁ G₁ F₂ G₂) :
    map₂ (CospanTransform.Hom.id psi) = 𝟙 (map psi) := sorry

/-- The full-subbicategory two-fibre-product action preserves vertical composition of cospan
modifications. -/
@[simp]
theorem map₂.comp
    (Gamma : Pseudofunctor.StrongTrans.Hom psi phi)
    (Delta : Pseudofunctor.StrongTrans.Hom phi chi) :
    map₂ (CospanTransform.Hom.comp Gamma Delta) =
      map₂ Gamma ≫ map₂ Delta := sorry

end TwoFibreProduct

end CategoryTheory
