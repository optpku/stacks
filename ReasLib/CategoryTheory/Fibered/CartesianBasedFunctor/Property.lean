module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Property
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Preservation of strongly cartesian morphisms

This module owns the neutral property that a based functor preserves strongly cartesian
morphisms, together with its closure under isomorphism, identity, and composition. It does not
depend on the bundled `CartesianBasedFunctor` owner or on equivalence-specific transport.
-/

@[expose] public section

universe u v uX vX uY vY uZ vZ

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace BasedFunctor

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- A based functor over `C` preserves strongly cartesian morphisms if it sends every strongly
cartesian arrow in the source to a strongly cartesian arrow in the target. -/
@[stacks 02XP "preservation property for fibred 1-morphisms"]
def PreservesStronglyCartesian (G : X ⥤ᵇ Y) : Prop :=
  ∀ ⦃a b : X.obj⦄ (φ : a ⟶ b),
    Functor.IsStronglyCartesian.property X.p φ →
      Functor.IsStronglyCartesian.property Y.p (G.map φ)

end BasedFunctor

namespace BasedFunctor.PreservesStronglyCartesian

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- Preservation of strongly cartesian arrows is invariant under isomorphism of based
functors. -/
instance isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      ((fun F : X ⥤ᵇ Y ↦ F.PreservesStronglyCartesian) :
        ObjectProperty (X ⥤ᵇ Y)) := sorry
/- Proof strategy: for an isomorphism `e : F ≅ G`, naturality expresses `G.map φ` as
`e.hom.app _ ≫ F.map φ ≫ e.inv.app _`. The components of a based natural isomorphism are
vertical isomorphisms, so strong cartesianness is preserved under pre- and postcomposition with
them. Apply the same argument to `e.symm` for the reverse transport. -/

/-- Identity based functors preserve strongly cartesian morphisms. -/
theorem id (X : BasedCategory.{vX, uX} C) :
    BasedFunctor.PreservesStronglyCartesian (𝟙 X) := sorry
/- Proof strategy: unfold `BasedFunctor.PreservesStronglyCartesian` and `BasedFunctor.id`;
the identity functor maps each arrow to itself, so the supplied `IsStronglyCartesian` hypothesis
is exactly the required conclusion. -/

/-- Composites of strongly-cartesian-preserving based functors again preserve strongly cartesian
morphisms. -/
theorem comp
    {Z : BasedCategory.{vZ, uZ} C} {F : X ⥤ᵇ Y} {G : Y ⥤ᵇ Z}
    (hF : BasedFunctor.PreservesStronglyCartesian F)
    (hG : BasedFunctor.PreservesStronglyCartesian G) :
    BasedFunctor.PreservesStronglyCartesian (F ⋙ G) := sorry
/- Proof strategy: unfold `BasedFunctor.PreservesStronglyCartesian` and `BasedFunctor.comp`, apply
`hF` to the source arrow, then apply `hG` to its image under `F`; the composite's map is the
iterated map by the definition of `BasedFunctor.comp`. -/

end BasedFunctor.PreservesStronglyCartesian

end CategoryTheory
