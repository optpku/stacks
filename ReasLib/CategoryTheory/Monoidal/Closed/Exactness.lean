/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import ReasLib.CategoryTheory.Functor.Exactness.Additive
public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness of internal Hom

Internal Hom preserves limits in its target and converts colimits in its source into limits.
For an abelian braided closed monoidal category, these facts give canonical additive and
left-exact functors in both variables, together with short-exact-sequence interfaces.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.MonoidalClosed

variable {A : Type u} [Category.{v} A] [MonoidalCategory A] [MonoidalClosed A]

/-- Internal Hom from a fixed source preserves all limits. -/
@[stacks 03EN "target variable"]
instance ihom_preservesLimits (F : A) : PreservesLimits (ihom F) := sorry

/-- In a braided closed category, internal Hom into a fixed target sends colimits in the
source to limits. -/
@[stacks 03EN "source variable"]
instance internalHomFlip_preservesLimits [BraidedCategory A] (G : A) :
    PreservesLimits ((internalHom (C := A)).flip.obj G : Aᵒᵖ ⥤ A) := sorry

section Abelian

variable [Abelian A]

/-- Internal Hom from a fixed source is left exact in its target variable. -/
theorem ihom_leftExact (F : A) : leftExactFunctor A A (ihom F) := sorry

/-- Internal Hom into a fixed target is left exact in its contravariant source variable. -/
theorem internalHomFlip_leftExact [BraidedCategory A] (G : A) :
    leftExactFunctor Aᵒᵖ A ((internalHom (C := A)).flip.obj G) := sorry

/-- Internal Hom from a fixed source is canonically additive in its target variable. -/
instance ihom_additive (F : A) : (ihom F).Additive := sorry

/-- Internal Hom into a fixed target is canonically additive in its contravariant source
variable. -/
instance internalHomFlip_additive [BraidedCategory A] (G : A) :
    ((internalHom (C := A)).flip.obj G).Additive := sorry

namespace InternalHom

/-- Internal Hom into a fixed target sends a right-exact short sequence in its source to a
left-exact short sequence. -/
@[stacks 0GMY "(1)"]
theorem mapOp_exact_of_exact_epi [BraidedCategory A]
    {S : ShortComplex A} (hS : S.Exact ∧ Epi S.g) (G : A) :
    (S.op.map ((internalHom (C := A)).flip.obj G)).Exact ∧
      Mono ((S.op.map ((internalHom (C := A)).flip.obj G)).f) := sorry

/-- Internal Hom from a fixed source sends a left-exact short sequence in its target to a
left-exact short sequence. -/
@[stacks 0GMY "(2)"]
theorem map_exact_of_exact_mono
    {S : ShortComplex A} (hS : S.Exact ∧ Mono S.f) (F : A) :
    (S.map (ihom F)).Exact ∧ Mono ((S.map (ihom F)).f) := sorry

end InternalHom

end Abelian

end CategoryTheory.MonoidalClosed
