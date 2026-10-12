/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Yoneda
public import stacks_project.Chap90.Remark_90_7_10_Adjunction

/-!
# Limit-preserving functors recover from the completion of their restriction

If `G : CompleteLocalAlgCat Λ k ⥤ Type w` commutes with limits, the unit
`typesCompletionUnit.app G` is an isomorphism. Representable functors are the
standard example.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- Remark 90.7.11 (1): if `G : CompleteLocalAlgCat Λ k ⥤ Type w` commutes with
limits, then the unit `typesCompletionUnit.app G` is an isomorphism. -/
@[stacks 06HE]
instance typesCompletionUnit_isIso (G : CompleteLocalAlgCat Λ k ⥤ Type w)
    [PreservesLimits G] : IsIso (typesCompletionUnit.app G) :=
  sorry

/-- Remark 90.7.11 (2): if `R : CompleteLocalAlgCat Λ k`, then
`typesCompletionUnit.app (coyoneda.obj (op R))` is an isomorphism, since the
representable functor `coyoneda.obj (op R)` commutes with limits. -/
@[stacks 06HE]
instance coyoneda_typesCompletionUnit_isIso (R : CompleteLocalAlgCat Λ k) :
    IsIso (typesCompletionUnit.app (coyoneda.obj (op R))) :=
  sorry

end CategoryTheory.Functor
