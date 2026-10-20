module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Precomposition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Precomposition of cartesian based functors

This module restricts heterogeneous precomposition of based functors to the full subcategories of
functors preserving strongly cartesian arrows. It is the universe-polymorphic Hom-category owner
used by universal properties of strictification and stackification.
-/

@[expose] public section

universe uC vC uS₁ vS₁ uS₂ vS₂ uS₃ vS₃ uS₄ vS₄

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]

namespace CartesianBasedFunctor

variable {S₁ : Type uS₁} {S₂ : Type uS₂} {S₃ : Type uS₃}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂] [Category.{vS₃} S₃]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

/-- Precomposition by a cartesian based functor on the heterogeneous categories of cartesian
based functors. -/
@[stacks 04W9 "cartesian precomposition on heterogeneous Hom-categories"]
def precomp (p₃ : S₃ ⥤ C) (F : CartesianBasedFunctor p₁ p₂) :
    CartesianBasedFunctor p₂ p₃ ⥤ CartesianBasedFunctor p₁ p₃ where
  obj G := F.comp G
  map {G H} η :=
    homMk ((BasedCategory.precomposition
      (BasedCategory.ofFunctor p₃) F.toBasedFunctor).map η.hom)
  map_id := sorry
  map_comp := sorry

/-- Heterogeneous cartesian precomposition acts on objects by composition. -/
@[simp, stacks 04W9 "object readout for cartesian precomposition"]
theorem precomp.obj (p₃ : S₃ ⥤ C) (F : CartesianBasedFunctor p₁ p₂)
    (G : CartesianBasedFunctor p₂ p₃) :
    (precomp p₃ F).obj G = F.comp G := sorry

/-- The underlying based natural transformation of cartesian precomposition is ordinary left
whiskering. -/
@[simp, stacks 04W9 "based morphism readout for cartesian precomposition"]
theorem precomp.map.hom
    (p₃ : S₃ ⥤ C) (F : CartesianBasedFunctor p₁ p₂)
    {G H : CartesianBasedFunctor p₂ p₃} (η : G ⟶ H) :
    ((precomp p₃ F).map η).hom =
      (BasedCategory.precomposition
        (BasedCategory.ofFunctor p₃) F.toBasedFunctor).map η.hom := sorry

/-- The underlying ordinary natural transformation of cartesian precomposition is the ordinary
natural transformation underlying left whiskering. -/
@[simp, stacks 04W9 "natural-transformation readout for cartesian precomposition"]
theorem precomp.map.toNatTrans
    (p₃ : S₃ ⥤ C) (F : CartesianBasedFunctor p₁ p₂)
    {G H : CartesianBasedFunctor p₂ p₃} (η : G ⟶ H) :
    ((precomp p₃ F).map η).hom.toNatTrans =
      ((BasedCategory.precomposition
        (BasedCategory.ofFunctor p₃) F.toBasedFunctor).map η.hom).toNatTrans := sorry

/-- A component of a precomposed cartesian natural transformation is the original component
evaluated at the image under the precomposing functor. -/
@[simp, stacks 04W9 "component readout for cartesian precomposition"]
theorem precomp.map.app
    (p₃ : S₃ ⥤ C) (F : CartesianBasedFunctor p₁ p₂)
    {G H : CartesianBasedFunctor p₂ p₃} (η : G ⟶ H) (x : S₁) :
    ((precomp p₃ F).map η).hom.toNatTrans.app x =
      η.hom.toNatTrans.app (F.toFunctor.obj x) := sorry

/-- Precomposition by the identity cartesian based functor is the identity on the corresponding
heterogeneous hom-category. -/
@[simp, stacks 04W9 "identity law for cartesian precomposition"]
theorem precomp.id (p₂ : S₂ ⥤ C) (p₁ : S₁ ⥤ C) :
    precomp p₂ (CartesianBasedFunctor.id p₁) =
      𝟭 (CartesianBasedFunctor p₁ p₂) := sorry

/-- Precomposition by a composite is the composite of the two precomposition functors in
contravariant order. -/
@[stacks 04W9 "composition law for cartesian precomposition"]
theorem precomp.comp
    {S₄ : Type uS₄} [Category.{vS₄} S₄] (p₄ : S₄ ⥤ C)
    {p₃ : S₃ ⥤ C} (F : CartesianBasedFunctor p₁ p₂)
    (G : CartesianBasedFunctor p₂ p₃) :
    precomp p₄ (F.comp G) = precomp p₄ G ⋙ precomp p₄ F := sorry

/- Axiom audit: the object and morphism maps of `precomp` are explicit. Its `sorryAx` dependency
is confined to the two Prop-valued functor laws. -/

end CartesianBasedFunctor

end CategoryTheory
