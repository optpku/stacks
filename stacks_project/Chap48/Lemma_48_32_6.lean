/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.Composition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 48.32.6: in Situation 48.16.1, for composable morphisms `f : X ⟶ Y` and
`g : Y ⟶ Z` of `FTS_S`, compactly supported derived pushforward is strictly
functorial: `Rg_! ∘ Rf_! = R(g ∘ f)_!`. -/
@[stacks 0G55]
#check (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.comp_isomorphic :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : AlgebraicGeometry.Scheme.Compactification.Of.UpperShriekCompChoice f g),
    Nonempty
      (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.compositeShriekHom f g C ≅
        AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.iteratedShriekHom f g C))
