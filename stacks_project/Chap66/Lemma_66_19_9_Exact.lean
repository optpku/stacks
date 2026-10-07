module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Pullback
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward

/-!
# Exactness of small étale inverse image for algebraic spaces

The inverse-image functors `f_small⁻¹` on abelian sheaves and on sheaves of sets for the
small étale sites of algebraic spaces are exact in the sense of Categories, Definition 4.23.1.
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
  sorry

/-- The opposite of étale base change admits left Kan extensions of abelian presheaves in
universe `u + 1`. -/
instance etaleBaseChange_op_hasLeftKanExtension_addCommGrp {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : (smallEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (etaleBaseChange f).op.HasLeftKanExtension F :=
  sorry

/-- The opposite of `spacesEtalePullback f` has left Kan extensions on abelian presheaves. -/
instance spacesEtalePullback_op_hasLeftKanExtension_addCommGrp {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (P : (spacesEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (spacesEtalePullback f).op.HasLeftKanExtension P :=
  sorry

variable {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Inverse image of abelian sheaves along `f_small` is an exact functor. -/
theorem smallEtaleInverseImage_exact_addCommGrp :
    exactFunctor _ _ (sheafInverseImage AddCommGrpCat.{u + 1} f) :=
  sorry

/-- Inverse image of abelian sheaves along `f_small` preserves finite limits. -/
instance smallEtaleInverseImage_preservesFiniteLimits_addCommGrp :
    PreservesFiniteLimits (sheafInverseImage AddCommGrpCat.{u + 1} f) :=
  sorry

/-- Inverse image of abelian sheaves along `f_small` preserves finite colimits. -/
instance smallEtaleInverseImage_preservesFiniteColimits_addCommGrp :
    PreservesFiniteColimits (sheafInverseImage AddCommGrpCat.{u + 1} f) :=
  sorry

/-- Inverse image of sheaves of sets along `f_small` is exact in the sense of Categories,
Definition 4.23.1. -/
theorem smallEtaleInverseImage_exact_type :
    exactFunctor _ _ (smallEtaleMorphismOfTopoi f).inverseImage :=
  sorry

/-- Inverse image of sheaves of sets along `f_small` preserves finite limits. -/
instance smallEtaleInverseImage_preservesFiniteLimits_type :
    PreservesFiniteLimits (smallEtaleMorphismOfTopoi f).inverseImage :=
  sorry

/-- Inverse image of sheaves of sets along `f_small` preserves finite colimits. -/
instance smallEtaleInverseImage_preservesFiniteColimits_type :
    PreservesFiniteColimits (smallEtaleMorphismOfTopoi f).inverseImage :=
  sorry

/-- Exactness of abelian inverse image is equivalent to preservation of finite limits and
finite colimits. -/
theorem smallEtaleInverseImage_exact_addCommGrp_iff :
    exactFunctor _ _ (sheafInverseImage AddCommGrpCat.{u + 1} f) ↔
      PreservesFiniteLimits (sheafInverseImage AddCommGrpCat.{u + 1} f) ∧
        PreservesFiniteColimits (sheafInverseImage AddCommGrpCat.{u + 1} f) :=
  sorry

/-- Exactness of set-valued inverse image is equivalent to preservation of finite limits and
finite colimits. -/
theorem smallEtaleInverseImage_exact_type_iff :
    exactFunctor _ _ (smallEtaleMorphismOfTopoi f).inverseImage ↔
      PreservesFiniteLimits (smallEtaleMorphismOfTopoi f).inverseImage ∧
        PreservesFiniteColimits (smallEtaleMorphismOfTopoi f).inverseImage :=
  sorry

/-- Inverse image of abelian sheaves along `f_spaces,étale` is an exact functor. -/
theorem spacesEtalePullback_sheafPullback_exact_addCommGrp :
    exactFunctor _ _
      ((spacesEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
        (spacesEtaleTopology Y) (spacesEtaleTopology X)) :=
  sorry

/-- Inverse image of sheaves of sets along `f_spaces,étale` is an exact functor. -/
theorem spacesEtalePullback_sheafPullback_exact_type :
    exactFunctor _ _
      ((spacesEtalePullback f).sheafPullback (Type (u + 1))
        (spacesEtaleTopology Y) (spacesEtaleTopology X)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
