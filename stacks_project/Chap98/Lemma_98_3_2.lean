/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap97.Lemma_97_6_3
public import stacks_project.Chap98.«98_13_2_1_Smooth»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Formal smoothness implies smoothness on predeformation categories

If `S` is locally Noetherian and `f : X ⟶ Y` is a 1-morphism of categories
fibred in groupoids over `(Sch/S)_fppf` that is formally smooth on objects,
representable by algebraic spaces and formally smooth, or representable by
algebraic spaces and smooth, then `f` is smooth on predeformations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 98.3.2 (1): if `S` is locally Noetherian and `f : X ⟶ Y` is a
1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
formally smooth on objects, then `f` is smooth on predeformations: for every
finite type field `k` over `S` and object `x0` of `X` over `k`, the functor
(98.3.1.1) is smooth in the sense of Definition 90.8.1. -/
@[stacks 07WK]
instance IsSmoothOnPredeformations.of_formallySmoothOnObjects
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [FormallySmoothOnObjects f] :
    IsSmoothOnPredeformations f :=
  sorry

/-- Lemma 98.3.2 (2): if `S` is locally Noetherian and `f : X ⟶ Y` is a
1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces and has the algebraic-space formally-smooth
property, then `f` is smooth on predeformations: for every finite type field
`k` over `S` and object `x0` of `X` over `k`, the functor (98.3.1.1) is
smooth in the sense of Definition 90.8.1. -/
@[stacks 07WK]
theorem IsSmoothOnPredeformations.of_has_formallySmooth
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    (h : has (@AlgebraicSpace.FormallySmooth S) f) :
    IsSmoothOnPredeformations f :=
  sorry

/-- Lemma 98.3.2 (3): if `S` is locally Noetherian and `f : X ⟶ Y` is a
1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces and smooth, then `f` is smooth on
predeformations: for every finite type field `k` over `S` and object `x0` of
`X` over `k`, the functor (98.3.1.1) is smooth in the sense of
Definition 90.8.1. -/
@[stacks 07WK]
instance IsSmoothOnPredeformations.of_smooth
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Smooth f] :
    IsSmoothOnPredeformations f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
