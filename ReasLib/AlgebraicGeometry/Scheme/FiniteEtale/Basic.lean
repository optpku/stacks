module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Limits.MorphismProperty
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
    HasFiniteLimits (FiniteEtale X) := by
  -- Local instance justification (native limit prerequisites): finite étale
  -- morphisms are stable under post-cancellation in the slice construction.
  letI : MorphismProperty.HasOfPostcompProperty
      finiteEtaleMorphism finiteEtaleMorphism :=
    { of_postcomp := by
        intro Y Z W f g hg hfg
        letI : IsFinite g := hg.1
        letI : IsFinite (f ≫ g) := hfg.1
        exact ⟨IsFinite.of_comp f g,
          MorphismProperty.of_postcomp (W := @Etale) f g hg.2 hfg.2⟩ }
  -- The terminal map and every pullback lift are the native scheme maps.
  letI : HasTerminal (FiniteEtale X) :=
    (MorphismProperty.Over.mkIdTerminal finiteEtaleMorphism X).hasTerminal
  letI : HasPullbacks (FiniteEtale X) :=
    MorphismProperty.Over.hasPullbacks finiteEtaleMorphism X
  exact hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- Base change on finite étale schemes preserves finite limits and finite colimits. -/
theorem finiteEtaleBaseChange_exact {X X' : Scheme.{u}} (f : X' ⟶ X) :
    exactFunctor (FiniteEtale X) (FiniteEtale X') (finiteEtaleBaseChange f) := sorry

/-- A dominant morphism induces a faithful base-change functor on finite étale schemes. -/
instance finiteEtaleBaseChange_faithful_of_isDominant {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] : (finiteEtaleBaseChange f).Faithful := sorry

end AlgebraicGeometry.Scheme
