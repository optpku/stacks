module

public import Mathlib.CategoryTheory.Abelian.Subobject

@[expose] public section

noncomputable section

open CategoryTheory.Limits

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace Subobject

/-- A subobject is essential if it has nonzero intersection with every nonzero
subobject of the same object. -/
def IsEssential {X : 𝒜} (A : Subobject X) : Prop :=
  ∀ B : Subobject X, B ≠ ⊥ → A ⊓ B ≠ ⊥

namespace IsEssential

/-- The defining nonzero-intersection criterion for an essential subobject. -/
theorem iff_inter_ne_bot {X : 𝒜} (A : Subobject X) :
    A.IsEssential ↔ ∀ B : Subobject X, B ≠ ⊥ → A ⊓ B ≠ ⊥ := sorry

/-- An essential subobject has nonzero intersection with every nonzero subobject. -/
theorem inter_ne_bot {X : 𝒜} {A B : Subobject X} (hA : A.IsEssential) (hB : B ≠ ⊥) :
    A ⊓ B ≠ ⊥ := sorry

end IsEssential

end Subobject

/-- An epimorphism is essential if a subobject of its source whose image is the whole
target must itself be the whole source. -/
class IsEssentialEpi {X Y : 𝒜} (f : X ⟶ Y) : Prop where
  epi : Epi f
  eq_top_of_image_eq_top (A : Subobject X) :
    imageSubobject (A.arrow ≫ f) = ⊤ → A = ⊤

namespace IsEssentialEpi

/-- An essential epimorphism is an epimorphism. -/
instance instEpi {X Y : 𝒜} {f : X ⟶ Y} [h : IsEssentialEpi f] : Epi f := h.epi

/-- Construct an essential epimorphism from epimorphy and subobject minimality. -/
theorem of {X Y : 𝒜} {f : X ⟶ Y} (h_epi : Epi f)
    (eq_top_of_image_eq_top : ∀ A : Subobject X,
      imageSubobject (A.arrow ≫ f) = ⊤ → A = ⊤) :
    IsEssentialEpi f := sorry

/-- An essential epimorphism is equivalently an epimorphism for which no proper
subobject of the source maps onto the target. -/
theorem iff_forall_proper {X Y : 𝒜} (f : X ⟶ Y) :
    IsEssentialEpi f ↔
      Epi f ∧ ∀ A : Subobject X,
        A ≠ ⊤ → imageSubobject (A.arrow ≫ f) ≠ ⊤ := sorry

end IsEssentialEpi

end CategoryTheory
