module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesTopos
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage

/-!
# Exactness of small étale inverse image for algebraic spaces

The inverse-image functors `f_small⁻¹` on abelian sheaves and on sheaves of sets for the
small étale sites of algebraic spaces preserve finite limits and finite colimits.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Abelian-group-valued weak sheafification exists in universe `u + 1` on the étale site of
algebraic spaces over `X`. -/
instance spacesEtaleTopology_hasWeakSheafify_addCommGrp (X : AlgebraicSpace S) :
    HasWeakSheafify (spacesEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (plusPlusAdjunction (spacesEtaleTopology X) AddCommGrpCat.{u + 1}).isRightAdjoint

/-- The opposite of étale base change admits left Kan extensions of abelian presheaves in
universe `u + 1`. -/
instance etaleBaseChange_op_hasLeftKanExtension_addCommGrp {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : (smallEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (etaleBaseChange f).op.HasLeftKanExtension F :=
  inferInstance

/-- The opposite of `spacesEtalePullback f` has left Kan extensions on abelian presheaves. -/
instance spacesEtalePullback_op_hasLeftKanExtension_addCommGrp {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (P : (spacesEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (spacesEtalePullback f).op.HasLeftKanExtension P :=
  inferInstance

variable {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Inverse image of abelian sheaves along `f_small` is an exact functor. -/
theorem smallEtaleInverseImage_exact_addCommGrp :
    exactFunctor _ _ (sheafInverseImage AddCommGrpCat.{u + 1} f) :=
  sorry

/-- Inverse image of abelian sheaves along `f_small` preserves finite limits. -/
instance smallEtaleInverseImage_preservesFiniteLimits_addCommGrp :
    PreservesFiniteLimits (sheafInverseImage AddCommGrpCat.{u + 1} f) :=
  (smallEtaleInverseImage_exact_addCommGrp f).1

/-- Inverse image of abelian sheaves along `f_small` preserves finite colimits. -/
instance smallEtaleInverseImage_preservesFiniteColimits_addCommGrp :
    PreservesFiniteColimits (sheafInverseImage AddCommGrpCat.{u + 1} f) :=
  (smallEtaleInverseImage_exact_addCommGrp f).2

/-- Inverse image of sheaves of sets along a morphism of algebraic spaces preserves finite
limits and finite colimits. -/
theorem smallEtaleInverseImage_exact_type :
    exactFunctor _ _ (smallEtaleMorphismOfTopoi f).inverseImage :=
  ⟨(smallEtaleMorphismOfTopoi f).inverseImagePreservesFiniteLimits,
    ⟨fun _ ↦ (smallEtaleMorphismOfTopoi f).adjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape⟩⟩

/-- Inverse image of sheaves of sets along `f_small` preserves finite limits. -/
instance smallEtaleInverseImage_preservesFiniteLimits_type :
    PreservesFiniteLimits (smallEtaleMorphismOfTopoi f).inverseImage :=
  (smallEtaleInverseImage_exact_type f).1

/-- Inverse image of sheaves of sets along `f_small` preserves finite colimits. -/
instance smallEtaleInverseImage_preservesFiniteColimits_type :
    PreservesFiniteColimits (smallEtaleMorphismOfTopoi f).inverseImage :=
  (smallEtaleInverseImage_exact_type f).2

end AlgebraicGeometry.AlgebraicSpace
