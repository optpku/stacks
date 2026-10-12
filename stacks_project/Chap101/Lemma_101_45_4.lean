/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap100.Lemma_100_9_12_Opens
public import stacks_project.Chap101.Definition_101_37_1_Proper
public import stacks_project.Chap101.Lemma_101_5_1
public import stacks_project.Chap101.Lemma_101_36_4_Unramified
public import stacks_project.Chap101.Lemma_101_45_5_Comparison
public import stacks_project.Chap101.Remark_101_19_5_AutomorphismGroup

/-!
# Openness of the automorphism-group isomorphism locus

If `f : X ⟶ Y` is representable by algebraic spaces and unramified, and
`I_Y ⟶ Y` is proper, then the set of points of `|X|` at which `f` induces an
isomorphism of automorphism groups is open. On the corresponding open
substack `U ⊂ X`, the inertia comparison `I_U ⟶ U ×_Y I_Y` is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.automorphismGroup

/-- The set of points of `|X|` at which `f` induces an isomorphism of
automorphism groups. -/
def isIsoAtLocus {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) : Set (Points X) :=
  {x | IsIsoAt f x}

/-- A point lies in `isIsoAtLocus f` if and only if `f` induces an isomorphism
of automorphism groups there. -/
theorem mem_isIsoAtLocus {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {x : Points X} :
    x ∈ isIsoAtLocus f ↔ IsIsoAt f x :=
  sorry

/-- Lemma 101.45.4 (1): if `f : X ⟶ Y` is a morphism of algebraic stacks that
is representable by algebraic spaces and unramified, and `I_Y ⟶ Y` is proper,
then the set of `x ∈ |X|` at which `f` induces an isomorphism of automorphism
groups is open. -/
@[stacks 0DUA]
theorem isOpen_isIsoAtLocus {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (h_repr : relativelyRepresentableByAlgebraicSpaces f) [Unramified f]
    [Proper (forget.{u + 1, u, u, u + 1} Y)] :
    IsOpen (isIsoAtLocus f) :=
  sorry

/-- The open substack of `X` occupying the automorphism-group isomorphism
locus of `f`. -/
def isIsoAtOpenSubstack {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (h : IsOpen (isIsoAtLocus f)) : OpenSubstack X :=
  OpenSubstack.ofOpens (Opens.mk (isIsoAtLocus f) h)

/-- The underlying point-set of `isIsoAtOpenSubstack f h` is
`isIsoAtLocus f`. -/
theorem pointsSet_isIsoAtOpenSubstack {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (h : IsOpen (isIsoAtLocus f)) :
    (isIsoAtOpenSubstack f h).pointsSet = isIsoAtLocus f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.automorphismGroup

namespace AlgebraicGeometry.AlgebraicStack.Inertia

/-- Lemma 101.45.4 (2): if `f : X ⟶ Y` is a morphism of algebraic stacks that
is representable by algebraic spaces and unramified, and `I_Y ⟶ Y` is proper,
then for an open substack `U ⊂ X` occupying the automorphism-group
isomorphism locus, the canonical 1-morphism
`comparison (U.ι ≫ f) : I_U ⟶ U ×_Y I_Y` is an isomorphism of stacks. -/
@[stacks 0DUA]
theorem comparison_isEquivalence_isIsoAtOpenSubstack {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (h_repr : relativelyRepresentableByAlgebraicSpaces f) [Unramified f]
    [Proper (forget.{u + 1, u, u, u + 1} Y)] (U : OpenSubstack X)
    (hU : U.pointsSet = automorphismGroup.isIsoAtLocus f) :
    (toBasedFunctor (comparison (U.ι ≫ f))).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Inertia
