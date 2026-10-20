/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Compact
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Brown Representability from a Detecting Factorization Set

This leaf isolates the abstract Brown-representability criterion from the
construction of one particular telescope or approximation tower.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite

universe v u

namespace CategoryTheory

namespace BrownRepresentability

section

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasCountableCoproducts D]

/-- Stacks 0GYG, Lemma 13.39.1: a set of objects satisfies the Brown-representability hypotheses
when it detects nonzero objects and maps from its members into countable coproducts factor
componentwise through countable coproducts of its members. -/
@[stacks 0GYG]
structure IsSet (S : Set D) : Prop where
  /-- Every nonzero object receives a nonzero morphism from a member of the set. -/
  detects_nonzero_objects {X : D} (hX : ¬ IsZero X) :
    ∃ E : D, E ∈ S ∧ ∃ f : E ⟶ X, f ≠ 0
  /-- Maps from a member into a countable coproduct factor componentwise through members. -/
  factors_through_countable_coproducts (X : ℕ → D) {E : D} (hE : E ∈ S) (α : E ⟶ ∐ X) :
    ∃ (E' : ℕ → D), (∀ n : ℕ, E' n ∈ S) ∧
      ∃ (β : ∀ n : ℕ, E' n ⟶ X n) (γ : E ⟶ ∐ E'),
        γ ≫ Limits.Sigma.map β = α

/-- Stacks 0GYG, Lemma 13.39.1: the set condition split into its detecting and
factorization clauses.  This is the componentwise interface used by downstream
constructions instead of rebuilding an `IsSet` structure literal. -/
@[stacks 0GYG "componentwise criterion"]
theorem isSet_iff (S : Set D) :
    IsSet S ↔
      (∀ {X : D}, ¬ IsZero X →
        ∃ E : D, E ∈ S ∧ ∃ f : E ⟶ X, f ≠ 0) ∧
      (∀ (X : ℕ → D) {E : D}, E ∈ S → (α : E ⟶ ∐ X) →
        ∃ (E' : ℕ → D), (∀ n : ℕ, E' n ∈ S) ∧
          ∃ (β : ∀ n : ℕ, E' n ⟶ X n) (γ : E ⟶ ∐ E'),
            γ ≫ Limits.Sigma.map β = α) := sorry

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{max u v} D]

/-- Stacks 0GYG, Lemma 13.39.1: a contravariant homological functor that sends direct sums to
products is represented when the source triangulated category has a Brown-representability set. -/
@[stacks 0GYG, stacks 0GZB "generic representability criterion"]
theorem existsRepresentation
    (S : Set D) (hS : IsSet S) (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hH : H.rightOp.IsHomological)
    [∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H] :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := sorry

/-- Explicit-preservation bridge for `existsRepresentation`; the canonical entry point uses
typeclass search for product preservation. -/
@[stacks 0GYG, stacks 0GZB "explicit preservation bridge"]
theorem existsRepresentation_of
    (S : Set D) (hS : IsSet S) (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := sorry

/-- The Brown-representability criterion also yields representability of the underlying
`Type`-valued functor, the standard form used by adjoint-functor arguments. -/
@[stacks 0GYG, stacks 0GZB "underlying representability"]
theorem isRepresentable
    (S : Set D) (hS : IsSet S) (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hH : H.rightOp.IsHomological)
    [∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H] :
    (H ⋙ forget AddCommGrpCat).IsRepresentable := sorry

/-- Explicit-preservation bridge for `isRepresentable`. -/
@[stacks 0GYG, stacks 0GZB "explicit representability bridge"]
theorem isRepresentable_of
    (S : Set D) (hS : IsSet S) (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    (H ⋙ forget AddCommGrpCat).IsRepresentable := sorry

/-- Universe-lifted bridge from Brown representability for consumers whose target `Type`
universe is fixed one level higher. -/
@[stacks 0GYG, stacks 0GZB "universe-lifted representability"]
theorem isRepresentableUlift
    (S : Set D) (hS : IsSet S) (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hH : H.rightOp.IsHomological)
    [∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H] :
    ((H ⋙ forget AddCommGrpCat) ⋙ uliftFunctor.{v}).IsRepresentable := sorry

/-- Explicit-preservation bridge for `isRepresentableUlift`. -/
@[stacks 0GYG, stacks 0GZB "explicit universe-lifted representability bridge"]
theorem isRepresentableUlift_of
    (S : Set D) (hS : IsSet S) (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    ((H ⋙ forget AddCommGrpCat) ⋙ uliftFunctor.{v}).IsRepresentable := sorry

/-- Stacks 0A8F, Lemma 13.38.1: a contravariant homological functor that sends coproducts to
products is represented on a compactly generated triangulated category. -/
@[stacks 0A8F]
theorem ofCompactGeneration (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hD : IsCompactlyGenerated D) (hH : H.rightOp.IsHomological)
    [∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H] :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := sorry

/-- Explicit-preservation bridge for compact-generation Brown representability. -/
@[stacks 0A8F "explicit preservation bridge"]
theorem ofCompactGeneration_of (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hD : IsCompactlyGenerated D) (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := sorry

/-- The compactly generated Brown theorem also gives representability of the underlying
`Type`-valued functor, the form used by adjoint-functor arguments. -/
@[stacks 0A8F]
theorem isRepresentable_ofCompactGeneration (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hD : IsCompactlyGenerated D) (hH : H.rightOp.IsHomological)
    [∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H] :
    (H ⋙ forget AddCommGrpCat).IsRepresentable := sorry

/-- Explicit-preservation bridge for the `Type`-valued compact-generation theorem. -/
@[stacks 0A8F "explicit representability bridge"]
theorem isRepresentable_ofCompactGeneration_of
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hD : IsCompactlyGenerated D) (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    (H ⋙ forget AddCommGrpCat).IsRepresentable := sorry

end

end BrownRepresentability

namespace Functor.Brown

universe v₁ v₂ u₁ u₂

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']

variable [_root_.CategoryTheory.IsTriangulated D]
  [_root_.CategoryTheory.IsTriangulated D']
  [HasCoproducts.{max u₁ v₁} D]

namespace Compact

/-- Stacks 0A8G: an exact coproduct-preserving functor out of a compactly generated
triangulated category is a left adjoint. -/
@[stacks 0A8G]
theorem isLeftAdjoint (hD : IsCompactlyGenerated D)
    (F : D ⥤ D') [LocallySmall.{v₁} D'] [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v₁), PreservesColimitsOfShape (Discrete J) F] :
    F.IsLeftAdjoint := sorry

/-- The right adjoint supplied by compact-generation Brown representability is triangulated for
the canonical shift comparison induced by its adjunction. -/
@[stacks 0A8G]
theorem hasTriangulatedRightAdjoint (hD : IsCompactlyGenerated D)
    (F : D ⥤ D') [LocallySmall.{v₁} D'] [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v₁), PreservesColimitsOfShape (Discrete J) F] :
    ∃ (G : D' ⥤ D) (adj : F ⊣ G),
      G.IsTriangulatedWith (adj.rightAdjointCommShift ℤ) := sorry

end Compact

namespace Set

/-- A Brown-representability set makes every exact coproduct-preserving functor out of the
source category a left adjoint. -/
@[stacks 0GZB "generic left-adjoint criterion"]
theorem isLeftAdjoint
    (F : D ⥤ D') [LocallySmall.{v₁} D'] [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v₁), PreservesColimitsOfShape (Discrete J) F]
    (hD : ∃ S : _root_.Set D, BrownRepresentability.IsSet S) :
    F.IsLeftAdjoint := sorry

/-- Stacks 0GYH: under the Brown-set hypothesis, an exact coproduct-preserving functor has a
triangulated right adjoint. -/
@[stacks 0GYH, stacks 0GZB "generic triangulated-right-adjoint criterion"]
theorem hasTriangulatedRightAdjoint
    (F : D ⥤ D') [LocallySmall.{v₁} D'] [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v₁), PreservesColimitsOfShape (Discrete J) F]
    (hD : ∃ S : _root_.Set D, BrownRepresentability.IsSet S) :
    ∃ (G : D' ⥤ D) (adj : F ⊣ G),
      G.IsTriangulatedWith (adj.rightAdjointCommShift ℤ) := sorry

end Set

end Functor.Brown

end CategoryTheory
