module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.NatTrans
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-cell action on locally induced two-fibre-product maps

Modifications of selected cospan transformations act on the induced maps through the locally
full hom categories. The computation API exposes the underlying pseudo-pullback components.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory ObjectProperty
open scoped Bicategory BasedFunctor Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]

namespace LocallyInduced.TwoFibreProduct

variable {P : ObjectProperty (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable {Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1)}
variable [Q.IsMultiplicative]
variable [BasedCategory.PseudoPullback.HomProperty.IsClosedUnder Q]
variable [Projections.Has (P := P) (Q := Q)]
variable [Q.IsClosedUnderIsomorphisms]
variable [Projections.IsDetected (P := P) (Q := Q)]
variable {X₁ Y₁ S₁ X₂ Y₂ S₂ : Bicategory.LocallyInducedBicategory
  (BasedCategory.{max v vB, max w (max u (max v vB))} C)
  (fun X : P.FullSubbicategory ↦ X.1) Q}
variable {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
variable {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}
variable {ψ φ : Bicategory.CospanTransform
  (B := Bicategory.LocallyInducedBicategory
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)
    (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂}

/-- A modification of selected cospan transformations induces the locally full `2`-morphism
between their explicit two-fibre-product maps. -/
@[stacks 0040 "modification action on locally induced two-fibre-product maps"]
noncomputable def map₂
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    map ψ ⟶ map φ :=
  ObjectProperty.homMk
    (BasedCategory.PseudoPullback.map₂ (CospanModification.forget Γ))

/-- Forgetting the induced locally full `2`-morphism recovers the explicit based
pseudo-pullback `2`-morphism. -/
@[simp]
theorem map₂.hom
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    (map₂ Γ).hom =
      BasedCategory.PseudoPullback.map₂ (CospanModification.forget Γ) := sorry

/-- The base component of an induced locally full two-fibre-product `2`-morphism is the
identity. -/
@[simp]
theorem map₂.base
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ)
    (A : (BasedCategory.PseudoPullback F₁.obj G₁.obj).obj) :
    BasedCategory.PseudoPullback.baseMap ((map₂ Γ).hom.toNatTrans.app A) =
      𝟙 (BasedCategory.PseudoPullback.baseObj A) := sorry

/-- The first component of an induced locally full two-fibre-product `2`-morphism is the
underlying left component of the cospan modification. -/
@[simp]
theorem map₂.fst
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ)
    (A : (BasedCategory.PseudoPullback F₁.obj G₁.obj).obj) :
    BasedCategory.PseudoPullback.fstMap ((map₂ Γ).hom.toNatTrans.app A) =
      (Bicategory.CospanTransform.Hom.left Γ).hom.toNatTrans.app
        (BasedCategory.PseudoPullback.fstObj A) := sorry

/-- The second component of an induced locally full two-fibre-product `2`-morphism is the
underlying right component of the cospan modification. -/
@[simp]
theorem map₂.snd
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ)
    (A : (BasedCategory.PseudoPullback F₁.obj G₁.obj).obj) :
    BasedCategory.PseudoPullback.sndMap ((map₂ Γ).hom.toNatTrans.app A) =
      (Bicategory.CospanTransform.Hom.right Γ).hom.toNatTrans.app
        (BasedCategory.PseudoPullback.sndObj A) := sorry

/-- Naturality of the induced locally full `2`-morphism on the explicit pseudo-pullback
carrier. -/
@[reassoc]
theorem map₂.naturality
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ)
    {A B : (BasedCategory.PseudoPullback F₁.obj G₁.obj).obj} (f : A ⟶ B) :
    (map ψ).obj.map f ≫ (map₂ Γ).hom.toNatTrans.app B =
      (map₂ Γ).hom.toNatTrans.app A ≫ (map φ).obj.map f := sorry

/-- Two induced locally full `2`-morphisms agree when all of their explicit pseudo-pullback
components agree. -/
theorem map₂.ext
    {Γ Δ : Pseudofunctor.StrongTrans.Hom ψ φ}
    (h : ∀ A : (BasedCategory.PseudoPullback F₁.obj G₁.obj).obj,
      (map₂ Γ).hom.toNatTrans.app A = (map₂ Δ).hom.toNatTrans.app A) :
    map₂ Γ = map₂ Δ := sorry

end LocallyInduced.TwoFibreProduct

end CategoryTheory
