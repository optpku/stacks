/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Limits.ExactFunctor

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A morphism property selecting finite étale morphisms of schemes. -/
abbrev finiteEtaleMorphism : MorphismProperty Scheme.{u} :=
  @IsFinite ⊓ @Etale

/-- The category of finite étale schemes over a fixed scheme. -/
abbrev FiniteEtale (X : Scheme.{u}) :=
  finiteEtaleMorphism.Over (⊤ : MorphismProperty Scheme.{u}) X

/-- Base change of finite étale schemes along a morphism of schemes. -/
noncomputable abbrev finiteEtaleBaseChange {X X' : Scheme.{u}} (f : X' ⟶ X) :
    FiniteEtale X ⥤ FiniteEtale X' :=
  MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) (⊤ : MorphismProperty Scheme.{u}) f

/-- The category of finite étale schemes over a scheme has finite limits. -/
instance finiteEtale_hasFiniteLimits (X : Scheme.{u}) :
    HasFiniteLimits (FiniteEtale X) := sorry

/-- The category of finite étale schemes over a scheme has finite colimits. -/
instance finiteEtale_hasFiniteColimits (X : Scheme.{u}) :
    HasFiniteColimits (FiniteEtale X) := sorry

/-- Base change on finite étale schemes preserves finite limits and finite colimits. -/
theorem finiteEtaleBaseChange_exact {X X' : Scheme.{u}} (f : X' ⟶ X) :
    exactFunctor (FiniteEtale X) (FiniteEtale X') (finiteEtaleBaseChange f) := sorry

/-- A dominant morphism induces a faithful base-change functor on finite étale schemes. -/
instance finiteEtaleBaseChange_faithful_of_isDominant {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] : (finiteEtaleBaseChange f).Faithful := sorry

end AlgebraicGeometry.Scheme
