module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.QuasiIso.Monoidal

/-!
# Derived tensor products from K-flat localization

@stack 0FPB

The derived symmetric monoidal structure is obtained by localizing the full subcategory of
K-flat homotopy objects at its restricted quasi-isomorphisms.  The source localization functor
is the inclusion of K-flat objects followed by `DerivedCategory.Qh`; no monoidality assertion is
made for all quasi-isomorphisms in the ambient homotopy category.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.KFlat

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]

/-- The localization functor from K-flat homotopy objects to the derived category. -/
@[stacks 0FPB "K-flat localization functor"]
noncomputable abbrev localizationFunctor :
    HomotopyCategory.KFlat C ⥤ DerivedCategory C :=
  (HomotopyCategory.kFlat C).ι ⋙
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)

/-- The proposition that the K-flat localization functor realizes localization at restricted
quasi-isomorphisms. -/
@[stacks 0FPB "localization condition"]
abbrev IsLocalization : Prop :=
  (localizationFunctor (C := C)).IsLocalization
    (HomotopyCategory.KFlat.quasiIso (C := C))

/-- The K-flat localization functor presents the derived category as the localization at
restricted quasi-isomorphisms. It is deliberately not an instance while the proof is a
placeholder, because localization lifts use this universal property to choose concrete data. -/
@[stacks 0FPB "K-flat localization model"]
theorem localizationIsLocalization [HomotopyCategory.KFlat.HasResolutions C] :
    IsLocalization (C := C) := sorry

section Monoidal

variable [HomotopyCategory.Koszul.TensorDescends (C := C)]
variable [HomotopyCategory.KFlat.TensorDescends (C := C)]
variable [IsLocalization (C := C)]

/-- The chosen tensor unit in the derived category is the image of the K-flat tensor unit. -/
@[stacks 0FPB "derived tensor unit"]
noncomputable def unitIso :
    (localizationFunctor (C := C)).obj (𝟙_ (HomotopyCategory.KFlat C)) ≅
      (localizationFunctor (C := C)).obj (𝟙_ (HomotopyCategory.KFlat C)) :=
  Iso.refl _

/-- The monoidal structure on the derived category induced by K-flat localization. -/
@[stacks 0FPB, stacks 0FNQ "derived tensor product", instance_reducible]
noncomputable instance monoidalCategory : MonoidalCategory (DerivedCategory C) :=
  inferInstanceAs
    (MonoidalCategory
      (LocalizedMonoidal (localizationFunctor (C := C))
        (HomotopyCategory.KFlat.quasiIso (C := C)) (unitIso (C := C))))

/-- The K-flat localization functor is strong monoidal for the derived tensor product. -/
@[implicit_reducible]
noncomputable instance localizationMonoidal :
    (localizationFunctor (C := C)).Monoidal :=
  inferInstanceAs
    ((Localization.Monoidal.toMonoidalCategory
      (localizationFunctor (C := C)) (HomotopyCategory.KFlat.quasiIso (C := C))
      (unitIso (C := C))).Monoidal)

/-- The symmetric structure on the derived category induced by the Koszul symmetry of K-flat
complexes. -/
@[stacks 0FPB, stacks 0FNQ "symmetric derived tensor product", implicit_reducible]
noncomputable instance symmetricCategory : SymmetricCategory (DerivedCategory C) :=
  inferInstanceAs
    (SymmetricCategory
      (LocalizedMonoidal (localizationFunctor (C := C))
        (HomotopyCategory.KFlat.quasiIso (C := C)) (unitIso (C := C))))

/-- The K-flat localization functor preserves the symmetric braiding. -/
@[implicit_reducible]
noncomputable instance localizationBraided :
    (localizationFunctor (C := C)).Braided :=
  inferInstanceAs
    ((Localization.Monoidal.toMonoidalCategory
      (localizationFunctor (C := C)) (HomotopyCategory.KFlat.quasiIso (C := C))
      (unitIso (C := C))).Braided)

/-- The unit comparison of the K-flat localization functor. -/
@[stacks 0FPB "derived tensor unit comparison"]
noncomputable def mapUnitIso :
    𝟙_ (DerivedCategory C) ≅
      (localizationFunctor (C := C)).obj (𝟙_ (HomotopyCategory.KFlat C)) :=
  Functor.Monoidal.εIso (localizationFunctor (C := C))

/-- The tensor comparison of the K-flat localization functor. -/
@[stacks 0FPB "derived tensor comparison"]
noncomputable def mapTensorIso (P Q : HomotopyCategory.KFlat C) :
    (localizationFunctor (C := C)).obj P ⊗
        (localizationFunctor (C := C)).obj Q ≅
      (localizationFunctor (C := C)).obj (P ⊗ Q) :=
  Functor.Monoidal.μIso (localizationFunctor (C := C)) P Q

end Monoidal

end CategoryTheory.DerivedCategory.KFlat



/- Axiom-audit boundary: the three class-shaped hypotheses on the concrete data declarations are
not synthesized from the placeholder theorems above. After forgetting the K-flat subtype proofs,
the tensor object, tensor morphisms, unit, and associator agree definitionally with their ambient
owners; their remaining `sorryAx` is confined to membership and coherence proof fields. -/
