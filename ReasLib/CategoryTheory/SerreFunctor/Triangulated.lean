/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.SerreFunctor.Uniqueness
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.SerreFunctor

variable {T : Type u} [Category.{v} T] [Preadditive T]

/-- The underlying functor of a Serre functor on a Hom-finite triangulated category admits
an explicit triangulated structure. -/
theorem hasTriangulatedStructure
    {k : Type w} [Field k] [Linear k T]
    [Limits.HasZeroObject T] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]
    (hfinite : ∀ X Y : T, FiniteDimensional k (X ⟶ Y))
    (S : SerreFunctor k T) :
    Functor.HasTriangulatedStructure S.toEquivalence.functor := sorry

end CategoryTheory.SerreFunctor

end
