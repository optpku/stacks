module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally surjective morphisms of presheaves

This leaf packages local surjectivity of type-valued presheaf morphisms as a
`MorphismProperty`.  The package is the topology-relative input used by generic
hypercovering constructions.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]

/-- Definition 25.6.1 (Tag 09VU): the morphism property of locally surjective
type-valued presheaf maps for a Grothendieck topology. -/
@[stacks 09VU "locally surjective presheaf morphisms"]
def locallySurjective (J : GrothendieckTopology C) :
    MorphismProperty (Cᵒᵖ ⥤ Type w) :=
  fun _ _ f ↦ IsLocallySurjective J f

/-- Membership in `locallySurjective J` is local surjectivity for `J`. -/
@[simp] theorem mem_locallySurjective_iff
    (J : GrothendieckTopology C) {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) :
    locallySurjective J f ↔ IsLocallySurjective J f := sorry

namespace locallySurjective

/-- Locally surjective presheaf morphisms contain identities and are closed
under composition. -/
instance isMultiplicative (J : GrothendieckTopology C) :
    (locallySurjective J : MorphismProperty (Cᵒᵖ ⥤ Type w)).IsMultiplicative := sorry

/-- Locally surjective presheaf morphisms are stable under base change. -/
instance isStableUnderBaseChange (J : GrothendieckTopology C) :
    (locallySurjective J : MorphismProperty (Cᵒᵖ ⥤ Type w)).IsStableUnderBaseChange := sorry

/-- Enlarging a Grothendieck topology preserves local surjectivity. -/
theorem monotone {J K : GrothendieckTopology C} (hJK : J ≤ K) :
    (locallySurjective J : MorphismProperty (Cᵒᵖ ⥤ Type w)) ≤
      locallySurjective K := sorry

end locallySurjective

end CategoryTheory.Presheaf
