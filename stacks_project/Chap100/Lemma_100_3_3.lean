/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage
public import stacks_project.Chap94.«94_9_8_1_Comparison»
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Testing representable morphisms of algebraic stacks on one fppf covering

A property of morphisms of algebraic spaces that is fppf local on the target
and stable under base change may be tested on the algebraic-space projection
of one surjective, flat, locally of finite presentation base change of a
morphism of algebraic stacks representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 100.3.3: Let `P` be a property of morphisms of algebraic spaces that is
fppf local on the target and stable under base change. Let `f : X ⟶ Y` be a
morphism of algebraic stacks representable by algebraic spaces. Let `W` be an
algebraic space and let `g : W.toGroupoids ⟶ Y` be surjective, locally of finite
presentation, and flat. If `v : V ⟶ W` represents the projection
`W ×_Y X ⟶ W`, then `f` has `P` if and only if `v` has `P`. -/
@[stacks 04XD]
theorem has_iff_of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    has P f ↔ P v :=
  sorry

namespace has

/-- If a morphism of algebraic spaces representing the base change of `f` along
a surjective, flat, locally of finite presentation morphism from an algebraic
space has `P`, then `f` has `P`. -/
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    P v → has P f :=
  sorry

/-- If `f` has `P`, then a morphism of algebraic spaces representing the base
change of `f` along a surjective, flat, locally of finite presentation morphism
from an algebraic space has `P`. -/
theorem covering_spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    has P f → P v :=
  sorry

end has

end AlgebraicGeometry.Groupoids.Hom
