/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap96.Lemma_96_19_10_Covering
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Covering lifts of representable surjective 1-morphisms

A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces, surjective, and either flat and locally of finite presentation
or smooth admits local lifts of every object after an fppf or étale covering.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 96.19.10 (1): Let `f : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `f` is representable by algebraic spaces,
surjective, flat, and locally of finite presentation, then for any object `y`
of `Y` there exists an fppf covering `{y_i ⟶ y}` and objects `x_i` of `X` such
that `f(x_i) ≅ y_i` in `Y`. -/
@[stacks 06XH]
theorem exists_fppfCovering_iso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) :
    existsCoveringLift StandardTopology.fppf f y :=
  sorry

/-- Lemma 96.19.10 (2): Let `f : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `f` is representable by algebraic spaces,
surjective, and smooth, then for any object `y` of `Y` there exists an étale
covering `{y_i ⟶ y}` and objects `x_i` of `X` such that `f(x_i) ≅ y_i` in `Y`. -/
@[stacks 06XH]
theorem exists_etaleCovering_iso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Surjective f] [Smooth f] {U : Over S}
    (y : GroupoidsOver.slice U ⟶ Y) :
    existsCoveringLift StandardTopology.etale f y :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
