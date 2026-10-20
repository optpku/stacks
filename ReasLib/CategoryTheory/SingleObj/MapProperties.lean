/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Tactic.CrossRefAttribute

/-!
# Categorical properties of one-object functors

This module reads faithfulness, fullness, full faithfulness, and equivalence of the functor
induced by a monoid homomorphism directly from the corresponding function-theoretic property.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace MonoidHom

variable {M : Type u} {N : Type v} [Monoid M] [Monoid N]

namespace toFunctor

/-- The one-object functor induced by a monoid homomorphism is faithful exactly when the
homomorphism is injective. -/
@[stacks 001F "faithfulness of a one-object functor"]
theorem faithful_iff_injective (p : M →* N) :
    p.toFunctor.Faithful ↔ Function.Injective p := sorry

/-- The one-object functor induced by a monoid homomorphism is full exactly when the homomorphism
is surjective. -/
theorem full_iff_surjective (p : M →* N) :
    p.toFunctor.Full ↔ Function.Surjective p := sorry

/-- The one-object functor induced by a monoid homomorphism is fully faithful exactly when the
homomorphism is bijective. -/
@[stacks 001F "full faithfulness of a one-object functor"]
theorem fullyFaithful_iff_bijective (p : M →* N) :
    Nonempty p.toFunctor.FullyFaithful ↔ Function.Bijective p := sorry

/-- The one-object functor induced by a monoid homomorphism is an equivalence exactly when the
homomorphism is bijective. -/
theorem isEquivalence_iff_bijective (p : M →* N) :
    p.toFunctor.IsEquivalence ↔ Function.Bijective p := sorry

section Groups

variable {G H : Type u} [Group G] [Group H]

/-- For a group homomorphism, full faithfulness of its one-object functor is equivalent to the
corresponding morphism in `GrpCat` being an isomorphism. -/
@[stacks 001F "full faithfulness of a one-object groupoid functor"]
theorem fullyFaithful_iff_isIso (p : G →* H) :
    Nonempty p.toFunctor.FullyFaithful ↔ IsIso (GrpCat.ofHom p) := sorry

/-- For a group homomorphism, equivalence of its one-object functor is equivalent to the
corresponding morphism in `GrpCat` being an isomorphism. -/
theorem isEquivalence_iff_isIso (p : G →* H) :
    p.toFunctor.IsEquivalence ↔ IsIso (GrpCat.ofHom p) := sorry

end Groups

end toFunctor
end MonoidHom
