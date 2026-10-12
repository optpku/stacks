/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import stacks_project.Chap61.Lemma_61_17_2_Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.24.1

Exactness of the small pro-étale abelian direct image along a finite morphism
of schemes which is locally of finite presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {Z X : Scheme.{u}} (f : Z ⟶ X)
variable [IsFinite f] [LocallyOfFinitePresentation f]

/-- The small pro-étale abelian direct image along a finite morphism of finite
presentation preserves finite limits. -/
instance smallPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (smallPushforward f) := sorry

variable [HasSheafify (topology Z) AddCommGrpCat.{u + 1}]
variable [HasSheafify (topology X) AddCommGrpCat.{u + 1}]

/-- The small pro-étale abelian direct image along a finite morphism of finite
presentation preserves finite colimits. -/
instance smallPushforward_preservesFiniteColimits :
    PreservesFiniteColimits (smallPushforward f) := sorry

/-- Bundled exact functor of abelian sheaves given by `smallPushforward` along a
finite morphism of finite presentation. -/
abbrev smallPushforwardExact :
    Sheaf (topology Z) AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (topology X) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (smallPushforward f)

/-- `smallPushforwardExact` is `ExactFunctor.of` of `smallPushforward`. -/
theorem smallPushforwardExact_eq :
    smallPushforwardExact f = ExactFunctor.of (smallPushforward f) := sorry

/-- Lemma 61.24.1: if `f : Z ⟶ X` is a finite morphism of schemes which is locally
of finite presentation, then
`smallPushforward f : Sheaf (topology Z) AddCommGrpCat ⥤ Sheaf (topology X) AddCommGrpCat`
is an exact functor. -/
@[stacks 09A8]
theorem smallPushforward_exact :
    exactFunctor (Sheaf (topology Z) AddCommGrpCat.{u + 1})
      (Sheaf (topology X) AddCommGrpCat.{u + 1}) (smallPushforward f) := sorry

end AlgebraicGeometry.Scheme.ProEt
