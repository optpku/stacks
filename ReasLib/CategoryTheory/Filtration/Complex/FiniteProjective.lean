/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective
public import ReasLib.CategoryTheory.Filtration.Complex.FiniteForget
public import ReasLib.CategoryTheory.Filtration.FiniteProjective

/-!
# Bounded filtered finite-projective complexes

Bounded cochain complexes whose terms are finite filtered finite-projective modules
have bounded finite-projective underlying and associated-graded complexes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open ComplexShape
open scoped FilteredObject.Finite ZeroObject

universe u

namespace CochainComplex

variable {Λ : Type u} [Ring Λ]

/-- A cochain complex of finite filtered left `Λ`-modules is bounded filtered finite
projective when it is bounded on both sides and each term is a filtered finite
projective object of `Filᶠ(ModuleCat Λ)`. -/
class IsBoundedFilteredFiniteProjective
    (P : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ) : Prop where
  /-- The complex is bounded on both sides. -/
  bounded : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b
  /-- Each term is a filtered finite projective object. -/
  filteredFiniteProjective (n : ℤ) :
    FilteredObject.IsFilteredFiniteProjective (P.X n).obj

/-- A cochain complex is bounded filtered finite projective exactly when it is bounded
and every term is filtered finite projective. -/
theorem isBoundedFilteredFiniteProjective_iff
    (P : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ) :
    IsBoundedFilteredFiniteProjective P ↔
      (∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧
        ∀ n : ℤ, FilteredObject.IsFilteredFiniteProjective (P.X n).obj :=
  sorry

/-- The zero complex of finite filtered modules is bounded filtered finite projective. -/
noncomputable instance instIsBoundedFilteredFiniteProjectiveZero :
    IsBoundedFilteredFiniteProjective (0 : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ) :=
  sorry

/-- Forgetting the finite filtration of a bounded filtered finite-projective complex
yields a bounded finite-projective cochain complex. -/
instance instIsBoundedFiniteProjective_forget
    (P : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ)
    [IsBoundedFilteredFiniteProjective P] :
    ((FilteredObject.Finite.Forget.cochain (ModuleCat.{u} Λ)).obj P).IsBoundedFiniteProjective :=
  sorry

end CochainComplex

namespace CategoryTheory.FilteredObject.Finite.GradedPiece

variable {Λ : Type u} [Ring Λ]

/-- Termwise `p`-th associated graded of a cochain complex of finite filtered modules. -/
noncomputable abbrev cochain (p : ℤ) :
    CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ ⥤ CochainComplex (ModuleCat.{u} Λ) ℤ :=
  AssociatedGraded.cochain (ModuleCat.{u} Λ) ⋙
    (GradedObject.eval p).mapHomologicalComplex (up ℤ)

end CategoryTheory.FilteredObject.Finite.GradedPiece

namespace CochainComplex

variable {Λ : Type u} [Ring Λ]

/-- Each associated-graded piece of a bounded filtered finite-projective complex is a
bounded finite-projective cochain complex. -/
instance instIsBoundedFiniteProjective_gradedPiece
    (P : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ)
    [IsBoundedFilteredFiniteProjective P] (p : ℤ) :
    ((FilteredObject.Finite.GradedPiece.cochain p).obj P).IsBoundedFiniteProjective :=
  sorry

end CochainComplex

