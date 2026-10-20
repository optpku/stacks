module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.HomPresheaf.LocallySurjective
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.LocalEquivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Gerbe morphisms of heterogeneous fibred projections

The gerbe-morphism property only uses a cartesian functor over a site: it is local essential
surjectivity on fiber objects together with local surjectivity on the minimally lifted canonical
Hom-presheaves. Neither a common universe for the total categories nor stack or groupoid
hypotheses belong to its owner.
-/

@[expose] public section

universe uC vC uS₁ vS₁ uS₂ vS₂ uS₃ vS₃

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {S₁ : Type uS₁} {S₂ : Type uS₂}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C} [p₁.IsFibered] [p₂.IsFibered]

namespace CartesianBasedFunctor

/-- A heterogeneous cartesian functor is a gerbe morphism when it is locally essentially
surjective on fiber objects and locally surjective on every minimally lifted canonical
Hom-presheaf. -/
@[stacks 06P2 "universe-polymorphic gerbe morphism"]
def IsGerbeMorphism
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂) : Prop :=
  LocallyEssentiallySurjective J F ∧ Homwise.IsLocallySurjective J F

/-- The two defining local conditions of a heterogeneous gerbe morphism. -/
@[stacks 06P2 "local criterion for a universe-polymorphic gerbe morphism"]
theorem isGerbeMorphism_iff
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂) :
    IsGerbeMorphism J F ↔
      LocallyEssentiallySurjective J F ∧ Homwise.IsLocallySurjective J F := sorry

/-- A heterogeneous cartesian functor is a gerbe morphism exactly when it is locally essentially
surjective on fiber objects and locally lifts fiber morphisms. -/
@[stacks 06P2 "local conditions for a universe-polymorphic gerbe morphism"]
theorem isGerbeMorphism_iff_localConditions
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂) :
    IsGerbeMorphism J F ↔
      LocallyEssentiallySurjective J F ∧ LocallyLifts J F := sorry

/-- A heterogeneous gerbe morphism is locally essentially surjective on fiber objects. -/
@[stacks 06P2 "objectwise local-surjectivity readout"]
theorem IsGerbeMorphism.locallyEssentiallySurjective
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂}
    (hF : IsGerbeMorphism J F) : LocallyEssentiallySurjective J F := sorry

/-- A heterogeneous gerbe morphism locally lifts fiber morphisms. -/
@[stacks 06P2 "local-lifting readout"]
theorem IsGerbeMorphism.locallyLifts
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂}
    (hF : IsGerbeMorphism J F) : LocallyLifts J F := sorry

/-- A heterogeneous gerbe morphism is locally surjective on every minimally lifted canonical
Hom-presheaf. -/
@[stacks 06P2 "Hom-presheaf local-surjectivity readout"]
theorem IsGerbeMorphism.homwiseLocallySurjective
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂}
    (hF : IsGerbeMorphism J F) : Homwise.IsLocallySurjective J F := sorry

/-- The identity cartesian based functor is a gerbe morphism. -/
@[stacks 06R3 "identity gerbe morphism"]
theorem IsGerbeMorphism.id (J : GrothendieckTopology C) :
    IsGerbeMorphism J (CartesianBasedFunctor.id p₁) := sorry

/-- Heterogeneous gerbe morphisms are closed under universe-polymorphic composition. -/
@[stacks 06R3 "composition of universe-polymorphic gerbe morphisms"]
theorem IsGerbeMorphism.comp
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C} [p₃.IsFibered]
    {J : GrothendieckTopology C}
    {F : CartesianBasedFunctor p₁ p₂} {G : CartesianBasedFunctor p₂ p₃}
    (hF : IsGerbeMorphism J F) (hG : IsGerbeMorphism J G) :
    IsGerbeMorphism J (F.comp G) := sorry

/-- The gerbe-morphism property is preserved when the topology is enlarged. -/
theorem IsGerbeMorphism.of_le
    {J K : GrothendieckTopology C} (hJK : J ≤ K)
    {F : CartesianBasedFunctor p₁ p₂} (hF : IsGerbeMorphism J F) :
    IsGerbeMorphism K F := sorry

/-- An equivalence over the base is a heterogeneous gerbe morphism. -/
theorem IsGerbeMorphism.of_isEquivalence
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂)
    (hF : F.toBasedFunctor.IsEquivalence) : IsGerbeMorphism J F := sorry

/-- Transport the gerbe-morphism property along an isomorphism of parallel heterogeneous
cartesian functors. -/
theorem IsGerbeMorphism.of_iso
    {J : GrothendieckTopology C} {F G : CartesianBasedFunctor p₁ p₂}
    (e : F ≅ G) (hF : IsGerbeMorphism J F) : IsGerbeMorphism J G := sorry

/-- Isomorphic parallel heterogeneous cartesian functors are gerbe morphisms simultaneously. -/
theorem isGerbeMorphism_iff_of_iso
    {J : GrothendieckTopology C} {F G : CartesianBasedFunctor p₁ p₂}
    (e : F ≅ G) : IsGerbeMorphism J F ↔ IsGerbeMorphism J G := sorry

end CartesianBasedFunctor

end CategoryTheory
