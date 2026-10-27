/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Algebra.Module.Pi
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.Transfer

/-!
# Instances for graded objects

This file transfers categorical structure from `C` to `GradedObject β C` through the canonical
equivalence with `Discrete β ⥤ C`.  Evaluation is registered as the pointwise additive,
finite-limit-preserving, and finite-colimit-preserving functor.
-/

@[expose] public section

open CategoryTheory Limits
open scoped CategoryTheory

universe w w' v' v u

namespace CategoryTheory

/-- The conventional notation `Gr(C)` for the category of integer-graded objects in `C`. -/
scoped notation "Gr(" C ")" => GradedObject ℤ C

namespace GradedObject

variable {β : Type w} {C : Type u} [Category.{v} C]

/-- Graded objects inherit their preadditive structure pointwise.  Its induced zero morphisms
agree definitionally with the canonical pointwise zero morphisms of `GradedObject`. -/
noncomputable instance preadditive [Preadditive C] : Preadditive (GradedObject β C) where
  homGroup := fun X Y ↦
    inferInstanceAs (AddCommGroup (∀ b : β, X b ⟶ Y b))
  add_comp _ _ _ f f' g := by
    funext p
    exact Preadditive.add_comp _ _ _ (f p) (f' p) (g p)
  comp_add _ _ _ f g g' := by
    funext p
    exact Preadditive.comp_add _ _ _ (f p) (g p) (g' p)

/-- Graded objects inherit an `R`-linear structure componentwise. -/
noncomputable instance linear {R : Type w'} [Semiring R] [Preadditive C] [Linear R C] :
    Linear R (GradedObject β C) where
  homModule X Y := inferInstanceAs (Module R (∀ b : β, X b ⟶ Y b))
  smul_comp _ _ _ r f g := by
    funext p
    exact Linear.smul_comp _ _ _ r (f p) (g p)
  comp_smul _ _ _ f r g := by
    funext p
    exact Linear.comp_smul _ _ _ (f p) r (g p)

namespace Preadditive

/-- The zero morphisms induced by the canonical pointwise preadditive structure on graded
objects. This is a named non-instance for APIs that require this exact presentation. -/
noncomputable abbrev zeroMorphisms [Preadditive C] : HasZeroMorphisms (GradedObject β C) :=
  @Preadditive.preadditiveHasZeroMorphisms (GradedObject β C) _ GradedObject.preadditive

end Preadditive

/-- Limits of graded objects are computed pointwise. -/
noncomputable instance hasLimitsOfShape (J : Type w') [Category.{v'} J]
    [HasLimitsOfShape J C] : HasLimitsOfShape J (GradedObject β C) :=
  Adjunction.hasLimitsOfShape_of_equivalence (piEquivalenceFunctorDiscrete β C).functor

/-- Colimits of graded objects are computed pointwise. -/
noncomputable instance hasColimitsOfShape (J : Type w') [Category.{v'} J]
    [HasColimitsOfShape J C] : HasColimitsOfShape J (GradedObject β C) :=
  Adjunction.hasColimitsOfShape_of_equivalence (piEquivalenceFunctorDiscrete β C).functor

/-- Finite products of graded objects are computed pointwise. -/
noncomputable instance hasFiniteProducts [HasFiniteProducts C] :
    HasFiniteProducts (GradedObject β C) :=
  ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence
    (piEquivalenceFunctorDiscrete β C).functor⟩

/-- Finite coproducts of graded objects are computed pointwise. -/
noncomputable instance hasFiniteCoproducts [HasFiniteCoproducts C] :
    HasFiniteCoproducts (GradedObject β C) :=
  ⟨fun _ => Adjunction.hasColimitsOfShape_of_equivalence
    (piEquivalenceFunctorDiscrete β C).functor⟩

/-- Finite limits of graded objects are computed pointwise. -/
noncomputable instance hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteLimits (GradedObject β C) :=
  ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence
    (piEquivalenceFunctorDiscrete β C).functor⟩

/-- Finite colimits of graded objects are computed pointwise. -/
noncomputable instance hasFiniteColimits [HasFiniteColimits C] :
    HasFiniteColimits (GradedObject β C) :=
  ⟨fun _ => Adjunction.hasColimitsOfShape_of_equivalence
    (piEquivalenceFunctorDiscrete β C).functor⟩

/-- Evaluation at a degree is additive. -/
instance evalAdditive [Preadditive C] (p : β) : (eval p : GradedObject β C ⥤ C).Additive where
  map_add := rfl

/-- Evaluation at a degree preserves zero morphisms. -/
instance evalPreservesZeroMorphisms [HasZeroMorphisms C] (p : β) :
    (eval p : GradedObject β C ⥤ C).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Evaluation at a degree is linear for the componentwise linear structure. -/
instance evalLinear {R : Type w'} [Semiring R] [Preadditive C] [Linear R C] (p : β) :
    Functor.Linear R (eval p : GradedObject β C ⥤ C) where
  map_smul _ _ := rfl

/-- Evaluation at a degree preserves finite limits. -/
noncomputable instance evalPreservesFiniteLimits [HasFiniteLimits C] (p : β) :
    PreservesFiniteLimits (eval p : GradedObject β C ⥤ C) := by
  refine @preservesFiniteLimits_of_natIso _ _ _ _ _ _
    (piEquivalenceFunctorDiscreteCompEvaluationIso C p) ?_
  exact comp_preservesFiniteLimits _ _

/-- Evaluation at a degree preserves finite colimits. -/
noncomputable instance evalPreservesFiniteColimits [HasFiniteColimits C] (p : β) :
    PreservesFiniteColimits (eval p : GradedObject β C ⥤ C) := by
  refine @preservesFiniteColimits_of_natIso _ _ _ _ _ _
    (piEquivalenceFunctorDiscreteCompEvaluationIso C p) ?_
  exact comp_preservesFiniteColimits _ _

/-- A morphism of graded objects is monic when every homogeneous component is monic. -/
theorem mono_of_mono_apply {X Y : GradedObject β C} (f : X ⟶ Y)
    [∀ p : β, Mono (f p)] : Mono f where
  right_cancellation g h w := by
    funext p
    exact (cancel_mono (f p)).1 (congrFun w p)

/-- A morphism of graded objects is epic when every homogeneous component is epic. -/
theorem epi_of_epi_apply {X Y : GradedObject β C} (f : X ⟶ Y)
    [∀ p : β, Epi (f p)] : Epi f where
  left_cancellation g h w := by
    funext p
    exact (cancel_epi (f p)).1 (congrFun w p)

/-- Graded objects in an abelian category form an abelian category. -/
@[stacks 0126]
noncomputable instance abelian [Abelian C] : Abelian (GradedObject β C) :=
  abelianOfEquivalence (piEquivalenceFunctorDiscrete β C).functor

end GradedObject

end CategoryTheory
