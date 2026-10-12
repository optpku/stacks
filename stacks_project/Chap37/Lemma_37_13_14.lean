/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.BaseChange.Homology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 37.13.14 (1): for a cartesian square of schemes, the canonical base-change map
from the pullback of `NL(f)` to `NL(f')` induces an isomorphism on `H⁰`. -/
@[stacks 0FV5] #check
  (@AlgebraicGeometry.Scheme.Hom.NaiveCotangent.BaseChange.map_zero_isIso_of_isPullback :
    ∀ {X X' Y Y' : AlgebraicGeometry.Scheme.{u}}
      {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      (hpb : IsPullback g' f' f g),
      IsIso (HomologicalComplex.homologyMap
        (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.BaseChange.map hpb.toCommSq) 0))

/- Lemma 37.13.14 (2): for a cartesian square of schemes, the canonical base-change map
from the pullback of `NL(f)` to `NL(f')` induces an epimorphism on `H⁻¹`. -/
@[stacks 0FV5] #check
  (@AlgebraicGeometry.Scheme.Hom.NaiveCotangent.BaseChange.map_negOne_epi_of_isPullback :
    ∀ {X X' Y Y' : AlgebraicGeometry.Scheme.{u}}
      {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      (hpb : IsPullback g' f' f g),
      Epi (HomologicalComplex.homologyMap
        (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.BaseChange.map hpb.toCommSq) (-1)))
