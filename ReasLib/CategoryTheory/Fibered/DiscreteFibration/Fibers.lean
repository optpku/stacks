/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Fiber characterizations of discrete fibrations

This file relates the intrinsic unique-lift owner to fibredness in groupoids and strict
discreteness of the standard fibers.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ uB vB

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor

namespace IsDiscreteFibration

/-- A discrete fibration is canonically fibred in groupoids.

Proof strategy: use unique lifts to prove that every chosen lift is strongly Cartesian, then apply
`Functor.IsFibered.of_exists_isStronglyCartesian`. Comparing an arbitrary total morphism with
the unique lift of its image proves that it is Cartesian. -/
@[stacks 0043 "a discrete fibration is fibred in groupoids"]
theorem toInGroupoids {p : S ⥤ C} (h : Functor.IsDiscreteFibration p) :
    Functor.IsFibered.InGroupoids p := sorry

/-- A discrete fibration is faithful: two arrows with the same image are two
lifts of the same base arrow with a common codomain, hence coincide by lift
uniqueness. -/
@[stacks 0043 "a discrete fibration is faithful"]
instance faithful (p : S ⥤ C) [Functor.IsDiscreteFibration p] :
    p.Faithful := sorry

/-- Typeclass-search form of
`Functor.IsDiscreteFibration.toInGroupoids`. -/
@[stacks 0043 "discrete-fibration groupoid instance"]
instance inGroupoids (p : S ⥤ C) [Functor.IsDiscreteFibration p] :
    Functor.IsFibered.InGroupoids p := sorry
/- Proof strategy: apply `toInGroupoids` to the supplied owner instance. -/

/-- Every standard fiber of a discrete fibration is a strictly
discrete category.

Proof strategy: a fiber morphism and the identity of its codomain both package as lifts of the
same base identity. Lift subsingletonity identifies the packages, hence their domain objects and
morphisms. These equalities provide `IsDiscrete.eq_of_hom` and the subsingleton hom-spaces. -/
@[stacks 04TM "the standard fibres are discrete"]
instance fiberIsDiscrete (p : S ⥤ C) [Functor.IsDiscreteFibration p] (U : C) :
    IsDiscrete (p.Fiber U) := sorry

end IsDiscreteFibration

/-- The unique-lift owner is exactly the source's formulation: a category fibred in groupoids
whose standard fibers are strictly discrete.

Proof strategy: the forward implication uses the canonical superclass and fiber instances above.
Conversely, factor two lifts through Cartesian lifts; discreteness of the relevant fiber identifies
the vertical comparison and its endpoints, proving both existence and subsingletonity of
`HomLift p f`. -/
theorem IsDiscreteFibration.iff_inGroupoids_fibersDiscrete (p : S ⥤ C) :
    Functor.IsDiscreteFibration p ↔
      Functor.IsFibered.InGroupoids p ∧ ∀ U : C, IsDiscrete (p.Fiber U) := sorry

/-- Fiberedness together with strictly discrete standard fibers constructs a discrete fibration.
This lower-level constructor is useful when fiberedness has been established before the
intermediate fibred-in-groupoids view.

Proof strategy: discrete fibers are groupoids, so
`Functor.IsFibered.InGroupoids.of_isFibered_fibersGroupoid` supplies the first component of
`IsDiscreteFibration.iff_inGroupoids_fibersDiscrete`; the second component is
`hfiber`. -/
theorem IsDiscreteFibration.of_isFibered_fibersDiscrete
    (p : S ⥤ C) (hp : p.IsFibered) (hfiber : ∀ U : C, IsDiscrete (p.Fiber U)) :
    Functor.IsDiscreteFibration p := sorry

/-- A functor is a discrete fibration exactly when it is fibered and all its standard fibers are
strictly discrete.

Proof strategy: combine
`Functor.IsFibered.InGroupoids.iff_isFibered_fibersGroupoid` with the source-semantic
characterization above; strict discreteness canonically supplies the groupoid structures. -/
theorem IsDiscreteFibration.iff_isFibered_fibersDiscrete (p : S ⥤ C) :
    Functor.IsDiscreteFibration p ↔ p.IsFibered ∧ ∀ U : C, IsDiscrete (p.Fiber U) := sorry

/-- Fibredness of a composite reflects to its first factor when the second
factor is a discrete fibration. -/
@[stacks 09WV "fibredness reflects along a discrete fibration"]
theorem IsFibered.of_comp_of_discreteFibration
    {B : Type uB} [Category.{vB} B]
    (F : S ⥤ B) (G : B ⥤ C) [G.IsDiscreteFibration]
    [(F ⋙ G).IsFibered] : F.IsFibered := sorry

end Functor

end CategoryTheory
