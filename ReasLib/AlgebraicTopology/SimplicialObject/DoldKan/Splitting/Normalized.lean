/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.Equivalence

/-!
# Mathlib's normalized Dold--Kan splitting

This module keeps the canonical Mathlib `Γ₀'` split-simplicial-object functor and its forgetful
comparison separate from the source-facing lower-face splitting. The two conventions are related
through the lower-face decomposition layer, not by redefining Mathlib's normalized object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace normalizedMoore.split

/-- Mathlib's packaged functorial splitting, using its normalized Moore convention for the
distinguished summands. -/
@[stacks 017U "normalized Moore split functor", stacks 017V "normalized Moore split functor"]
abbrev functor : SimplicialObject A ⥤ Split A :=
  Abelian.DoldKan.N ⋙ AlgebraicTopology.DoldKan.Γ₀'

/-- Forgetting Mathlib's packaged normalized Moore splitting recovers the original simplicial
object up to the Dold--Kan unit isomorphism. -/
@[stacks 017U "forgetful normalized Moore splitting comparison",
  stacks 017V "forgetful normalized Moore splitting comparison"]
def forgetIso :
    functor (A := A) ⋙ Split.forget A ≅ 𝟭 (SimplicialObject A) :=
  (Functor.associator Abelian.DoldKan.N AlgebraicTopology.DoldKan.Γ₀'
      (Split.forget A)).symm ≪≫
    Abelian.DoldKan.equivalence.unitIso.symm

/-- The distinguished degree-`n` summand in Mathlib's packaged splitting is its normalized Moore
subobject. -/
@[simp, stacks 017U "normalized Moore splitting summand",
  stacks 017V "normalized Moore splitting summand"]
theorem functor.obj.summand (U : SimplicialObject A) (n : ℕ) :
    ((functor (A := A)).obj U).s.N n =
      (NormalizedMooreComplex.objX U n : A) := sorry

end normalizedMoore.split

end CategoryTheory.SimplicialObject
