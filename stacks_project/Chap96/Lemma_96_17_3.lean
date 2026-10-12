/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Fibre products and equalizers along 1-morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` preserves
fibre products. If it is faithful, it also preserves equalizers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

/-- Lemma 96.17.3 (1): a 1-morphism `f : X ⟶ Y` of categories fibred in groupoids
over `(Sch/S)_fppf` transforms fibre products into fibre products, i.e.
`toFunctor f` preserves limits of shape `WalkingCospan`. -/
@[stacks 06WZ]
instance preservesPullbacks (f : X ⟶ Y) :
    PreservesLimitsOfShape WalkingCospan (toFunctor f) := sorry

/-- Lemma 96.17.3 (2): if a 1-morphism `f : X ⟶ Y` of categories fibred in
groupoids over `(Sch/S)_fppf` is faithful, then `f` transforms equalizers into
equalizers, i.e. `toFunctor f` preserves limits of shape `WalkingParallelPair`. -/
@[stacks 06WZ]
instance preservesEqualizers (f : X ⟶ Y) [Functor.Faithful (toFunctor f)] :
    PreservesLimitsOfShape WalkingParallelPair (toFunctor f) := sorry

end AlgebraicGeometry.GroupoidsOver
