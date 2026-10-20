module

public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! # Cartesian factor maps in a groupoid-valued co-Grothendieck construction

The canonical lifted object and arrow are Mathlib's reindexing and identity-fibre
arrow. For any other arrow, the factor is the native Cartesian factor followed
by the inverse of its supplied fibre isomorphism.
-/

@[expose] public section

noncomputable section

universe u v uF vF

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open Opposite Functor
open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]
variable (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF})
variable [∀ U, IsGroupoid (F.obj U)]

/-- An arrow's fibre isomorphism, viewed in the total category over its original base.
Its inverse is the actual inverse in the supplied groupoid fibre. -/
def fiberIso {a b : ∫ᶜ F} (φ : a ⟶ b) :
    a ≅ domainCartesianLift b.fiber φ.base :=
  (ι F a.base).mapIso (asIso φ.fiber)

/-- The actual factor over `g`: first factor through the native Cartesian lift,
then use the inverse of the original arrow's fibre isomorphism. -/
def factorMap {a b a' : ∫ᶜ F} (φ : a ⟶ b) (g : a'.base ⟶ a.base)
    (τ : a' ⟶ b) (hτ : (forget F).IsHomLift (g ≫ φ.base) τ) : a' ⟶ a :=
  letI := hτ
  homCartesianLift φ.base g τ ≫ (fiberIso F φ).inv

/-- The displayed factor lies over the prescribed base arrow. -/
theorem factorMap_isHomLift {a b a' : ∫ᶜ F} (φ : a ⟶ b)
    (g : a'.base ⟶ a.base) (τ : a' ⟶ b)
    (hτ : (forget F).IsHomLift (g ≫ φ.base) τ) :
    (forget F).IsHomLift g (factorMap F φ g τ hτ) := sorry

/-- Composing the displayed factor with the original arrow recovers the input. -/
theorem factorMap_fac {a b a' : ∫ᶜ F} (φ : a ⟶ b)
    (g : a'.base ⟶ a.base) (τ : a' ⟶ b)
    (hτ : (forget F).IsHomLift (g ≫ φ.base) τ) :
    factorMap F φ g τ hτ ≫ φ = τ := sorry

/-- The factor over a fixed base arrow is unique. -/
theorem factorMap_unique {a b a' : ∫ᶜ F} (φ : a ⟶ b)
    (g : a'.base ⟶ a.base) (τ : a' ⟶ b)
    (χ : a' ⟶ a) (hχbase : (forget F).IsHomLift g χ) (hχ : χ ≫ φ = τ)
    (hτ : (forget F).IsHomLift (g ≫ φ.base) τ) :
    χ = factorMap F φ g τ hτ := sorry

/-- Every arrow is strongly Cartesian, with its actual factor as universal witness. -/
theorem arrowIsStronglyCartesian {a b : ∫ᶜ F} (φ : a ⟶ b) :
    (forget F).IsStronglyCartesian φ.base φ where
  toIsHomLift := IsHomLift.map (forget F) φ
  universal_property' := by
    intro a' g τ hτ
    exact ⟨factorMap F φ g τ hτ,
      ⟨factorMap_isHomLift F φ g τ hτ, factorMap_fac F φ g τ hτ⟩,
      fun χ hχ => factorMap_unique F φ g τ χ hχ.1 hχ.2 hτ⟩

/-- Every arrow is Cartesian using the same specified strong factor map. -/
theorem arrowIsCartesian {a b : ∫ᶜ F} (φ : a ⟶ b) :
    (forget F).IsCartesian ((forget F).map φ) φ := by
  letI : (forget F).IsStronglyCartesian φ.base φ := arrowIsStronglyCartesian F φ
  exact Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian (forget F) φ.base φ

end CategoryTheory.Pseudofunctor.CoGrothendieck
