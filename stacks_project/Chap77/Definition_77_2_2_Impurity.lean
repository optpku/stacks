/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap71.Lemma_71_4_6_RelativeAssassin

/-!
# Impurities of modules on algebraic spaces

An impurity of a module above a point records a scheme-valued base change, a
specialization ending above that point, and a relative associated point of the
pulled-back module whose closure misses the fibre over the special endpoint.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- An impurity of an `𝒪_X`-module `F` above a point `y` of `Y` records a scheme
`T` over `S`, a morphism `g : ofOver T ⟶ Y`, a specialization of points of `T`
ending above `y`, and a point of `|Limits.pullback f g|` in the relative assassin
of the pulled-back module whose closure misses the fibre over the special
endpoint. -/
structure Impurity (F : X.Modules) (f : X ⟶ Y) (y : Points Y) where
  /-- The scheme over `S` used for the base change. -/
  T : Over S
  /-- The base-change morphism. -/
  g : ofOver T ⟶ Y
  /-- The generic endpoint of the specialization. -/
  genericPoint : T.left
  /-- The special endpoint of the specialization. -/
  specialPoint : T.left
  /-- The chosen specialization in `T`. -/
  specializes : Specializes genericPoint specialPoint
  /-- The special endpoint lies above `y`. -/
  map_specialPoint : Points.map g (ofOver.pointsEquiv T specialPoint) = y
  /-- The chosen point of `X ×_Y T`. -/
  point : Points (Limits.pullback f g)
  /-- The chosen point lies above the generic endpoint. -/
  map_point :
    Points.map (Limits.pullback.snd f g) point = ofOver.pointsEquiv T genericPoint
  /-- The point belongs to the relative assassin of the pulled-back module. -/
  mem_relativeAssassin :
    point ∈ relativeAssassin (Limits.pullback.snd f g)
      ((Modules.pullback (Limits.pullback.fst f g)).obj F)
  /-- The closure of the chosen point misses the fibre over the special endpoint. -/
  closure_disjoint_fiber :
    Disjoint (closure {point})
      (Points.map (Limits.pullback.snd f g) ⁻¹' {ofOver.pointsEquiv T specialPoint})

namespace Impurity

variable {F : X.Modules} {f : X ⟶ Y} {y : Points Y}

/-- Construct an impurity from a scheme-valued base change, a specialization, a
point of the pullback, and the defining incidence, associated-point, and
disjointness conditions. -/
def of (T : Over S) (g : ofOver T ⟶ Y) (genericPoint specialPoint : T.left)
    (specializes : Specializes genericPoint specialPoint)
    (map_specialPoint : Points.map g (ofOver.pointsEquiv T specialPoint) = y)
    (point : Points (Limits.pullback f g))
    (map_point :
      Points.map (Limits.pullback.snd f g) point = ofOver.pointsEquiv T genericPoint)
    (mem_relativeAssassin :
      point ∈ relativeAssassin (Limits.pullback.snd f g)
        ((Modules.pullback (Limits.pullback.fst f g)).obj F))
    (closure_disjoint_fiber :
      Disjoint (closure {point})
        (Points.map (Limits.pullback.snd f g) ⁻¹'
          {ofOver.pointsEquiv T specialPoint})) :
    Impurity F f y where
  T := T
  g := g
  genericPoint := genericPoint
  specialPoint := specialPoint
  specializes := specializes
  map_specialPoint := map_specialPoint
  point := point
  map_point := map_point
  mem_relativeAssassin := mem_relativeAssassin
  closure_disjoint_fiber := closure_disjoint_fiber

/-- The defining specialization, lying-over, associated-point, and disjointness
conditions carried by an impurity. -/
theorem spec (I : Impurity F f y) :
    Specializes I.genericPoint I.specialPoint ∧
      Points.map I.g (ofOver.pointsEquiv I.T I.specialPoint) = y ∧
      Points.map (Limits.pullback.snd f I.g) I.point =
        ofOver.pointsEquiv I.T I.genericPoint ∧
      I.point ∈ relativeAssassin (Limits.pullback.snd f I.g)
          ((Modules.pullback (Limits.pullback.fst f I.g)).obj F) ∧
      Disjoint (closure {I.point})
        (Points.map (Limits.pullback.snd f I.g) ⁻¹'
          {ofOver.pointsEquiv I.T I.specialPoint}) := sorry

/-- The special endpoint of an impurity is not in the image of the closure of the
chosen point under the base-changed morphism. -/
theorem not_mem_image_closure (I : Impurity F f y) :
    ofOver.pointsEquiv I.T I.specialPoint ∉
      Points.map (Limits.pullback.snd f I.g) '' closure {I.point} := sorry

/-- No specialization of the chosen point of an impurity lies over the special
endpoint. -/
theorem not_exists_specializes_fiber (I : Impurity F f y) :
    ¬ ∃ θ : Points (Limits.pullback f I.g),
      Specializes I.point θ ∧
        Points.map (Limits.pullback.snd f I.g) θ =
          ofOver.pointsEquiv I.T I.specialPoint := sorry

end Impurity

end AlgebraicGeometry.AlgebraicSpace.Modules
