/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Yoneda
public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion.Adjunction

/-!
# Continuity of completion for limit-preserving functors

Limit-preserving functors on complete local algebras are recovered from the
completion of their restriction to Artinian local algebras.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- A limit-preserving functor is recovered by the completion of its restriction. -/
instance typesCompletionUnit_isIso (G : CompleteLocalAlgCat Λ k ⥤ Type w)
    [PreservesLimits G] : IsIso (typesCompletionUnit.app G) :=
  sorry

/-- The completion unit is an isomorphism for every representable functor. -/
instance coyoneda_typesCompletionUnit_isIso (R : CompleteLocalAlgCat Λ k) :
    IsIso (typesCompletionUnit.app (coyoneda.obj (op R))) :=
  typesCompletionUnit_isIso (coyoneda.obj (op R))

end CategoryTheory.Functor
