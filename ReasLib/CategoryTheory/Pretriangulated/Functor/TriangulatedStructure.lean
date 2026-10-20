/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Triangulated Structure on a Functor

Mathlib's `Functor.IsTriangulated` is a typeclass because it is used to form
the triangle-level action of a functor. This leaf provides Prop-valued views
when a theorem must assert that some, not canonically chosen, shift comparison
makes a functor triangulated.
-/

open CategoryTheory

universe v u
universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u} {D : Type v} [Category C] [Category D]
  [HasShift C ℤ] [HasShift D ℤ]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- A specified shift comparison makes `F` a triangulated functor. This is
the explicit-parameter form of Mathlib's typeclass `Functor.IsTriangulated`. -/
@[stacks 014W]
def IsTriangulatedWith (F : C ⥤ D) (h : F.CommShift ℤ) : Prop :=
  @Functor.IsTriangulated C D _ _ _ _ F h _ _ _ _ _ _ _ _

/-- A functor admits a shift comparison making it triangulated. Unlike a
global instance, this Prop does not choose noncanonical `CommShift` data. -/
@[stacks 014W]
def HasTriangulatedStructure (F : C ⥤ D) : Prop :=
  ∃ h : F.CommShift ℤ, F.IsTriangulatedWith h

/-- The explicit view of `IsTriangulatedWith` is Mathlib's triangulated
functor class applied to its specified shift comparison. -/
theorem isTriangulatedWith_iff (F : C ⥤ D) (h : F.CommShift ℤ) :
    F.IsTriangulatedWith h ↔
      @Functor.IsTriangulated C D _ _ _ _ F h _ _ _ _ _ _ _ _ := sorry

section Precomposition

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₃ ℤ]
  [Limits.HasZeroObject C₁] [Limits.HasZeroObject C₂] [Limits.HasZeroObject C₃]
  [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive]
  [∀ n : ℤ, (shiftFunctor C₂ n).Additive]
  [∀ n : ℤ, (shiftFunctor C₃ n).Additive]
  [Pretriangulated C₁] [Pretriangulated C₂] [Pretriangulated C₃]

/-- Triangulated structures compose.  The existential presentation keeps the comparison data
out of global typeclass search while exposing the standard closure property to downstream APIs. -/
@[stacks 014W "composition of triangulated functors"]
theorem HasTriangulatedStructure.comp
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    (hF : F.HasTriangulatedStructure) (hG : G.HasTriangulatedStructure) :
    (F ⋙ G).HasTriangulatedStructure := sorry

/-- Exactness of a functor is reflected by precomposition with
an exact functor whose induced map on arrows is essentially surjective. The
factorization is deliberately expressed by a natural isomorphism, since a
universal lift rarely gives a definitional equality of functors. -/
@[stacks 05R7]
theorem hasTriangulatedStructure_of_precomp_iso
    (P : C₁ ⥤ C₂) [P.CommShift ℤ] [P.IsTriangulated] [P.mapArrow.EssSurj]
    (F : C₁ ⥤ C₃) (hF : F.HasTriangulatedStructure)
    (G : C₂ ⥤ C₃) (hfac : P ⋙ G ≅ F) :
    G.HasTriangulatedStructure := sorry

end Precomposition

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C : Type u} {D : Type v} [Category C] [Category D]
  [HasShift C ℤ] [HasShift D ℤ]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  {F : C ⥤ D} {G : D ⥤ C}

/-- The explicit-parameter form of exactness for the right adjoint of an exact functor.
The shift comparison is the canonical one induced by the adjunction. -/
@[stacks 0A8D]
theorem isTriangulatedWith_rightAdjoint (adj : F ⊣ G)
    [F.CommShift ℤ] [F.IsTriangulated] :
    G.IsTriangulatedWith (adj.rightAdjointCommShift ℤ) := sorry

end CategoryTheory.Adjunction
