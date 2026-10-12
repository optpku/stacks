/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Criteria
public import ReasLib.CategoryTheory.Fibered.InGroupoids
public import ReasLib.CategoryTheory.Fibered.SingleObj.KernelFiber.Equivalence

/-!
# Fibredness criteria for one-object functors

This module characterizes fibredness, and fibredness in groupoids, of the one-object functor
induced by a group homomorphism in terms of surjectivity.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor

universe u v

namespace MonoidHom

variable {G : Type u} {H : Type v} [Group G] [Group H]

namespace toFunctor

/-- The one-object functor induced by a group homomorphism is fibered exactly when the
homomorphism is surjective. -/
@[stacks 003U "one-object fibredness is surjectivity"]
theorem isFibered_iff_surjective (p : G →* H) :
    p.toFunctor.IsFibered ↔ Function.Surjective p := sorry

/-- A surjective group homomorphism induces a fibered one-object functor. -/
theorem isFibered_of_surjective
    (p : G →* H) (hp : Function.Surjective p) :
    p.toFunctor.IsFibered := sorry

/-- Fibredness of the induced one-object functor forces the group homomorphism to be
surjective. -/
theorem surjective_of_isFibered
    (p : G →* H) [p.toFunctor.IsFibered] :
    Function.Surjective p := sorry

/-- The one-object functor induced by a group homomorphism is fibred in groupoids exactly when
the homomorphism is surjective. -/
@[stacks 003U "one-object groupoid fibredness is surjectivity"]
theorem inGroupoids_iff_surjective (p : G →* H) :
    Functor.IsFibered.InGroupoids p.toFunctor ↔ Function.Surjective p := sorry

/-- A surjective group homomorphism induces a one-object functor fibred in groupoids. -/
theorem inGroupoids_of_surjective
    (p : G →* H) (hp : Function.Surjective p) :
    Functor.IsFibered.InGroupoids p.toFunctor := sorry

/-- A one-object functor fibred in groupoids comes from a surjective group homomorphism. -/
theorem surjective_of_inGroupoids
    (p : G →* H) [Functor.IsFibered.InGroupoids p.toFunctor] :
    Function.Surjective p := sorry

end toFunctor

end MonoidHom
