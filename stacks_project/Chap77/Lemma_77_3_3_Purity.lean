/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Topology.Specialization
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Lemma_66_29_2
public import stacks_project.Chap67.Definition_67_27_1_QuasiFinite
public import stacks_project.Chap67.Lemma_67_15_2
public import stacks_project.Chap67.Lemma_67_23_3_Pullback
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap71.Lemma_71_4_6_RelativeAssassin

/-!
# Purity of modules along a fibre of a morphism of algebraic spaces

A finite type quasi-coherent module on a finite type decent morphism of algebraic
spaces is pure above a point of the base when it admits no scheme-valued impurity
that is quasi-finite at the special point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A finite type quasi-coherent module on a finite type decent morphism of
algebraic spaces is pure above a point of the base when it admits no
scheme-valued impurity that is quasi-finite at the special point. -/
def IsPureAlong {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules)
    (f : X ⟶ Y) [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType]
    (y : |Y|) : Prop :=
  ∀ (T : Over S) (h : ofOver T ⟶ Y) (t' t : T.left)
      (ξ : Points (Limits.pullback f h)),
    ¬ (Specializes t' t ∧
        Points.map h (ofOver.pointsEquiv T t) = y ∧
        Points.map (Limits.pullback.snd f h) ξ = ofOver.pointsEquiv T t' ∧
        FiniteType.QuasiFiniteAt h (ofOver.pointsEquiv T t) ∧
        ξ ∈ relativeAssassin (Limits.pullback.snd f h)
          ((pullback (Limits.pullback.fst f h)).obj F) ∧
        ofOver.pointsEquiv T t ∉
          Points.map (Limits.pullback.snd f h) '' closure {ξ})

/-- Purity above a point of the base is the absence of scheme-valued impurities
that are quasi-finite at the special point. -/
theorem isPureAlong_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : |Y|) :
    IsPureAlong F f y ↔
      ∀ (T : Over S) (h : ofOver T ⟶ Y) (t' t : T.left)
          (ξ : Points (Limits.pullback f h)),
        ¬ (Specializes t' t ∧
            Points.map h (ofOver.pointsEquiv T t) = y ∧
            Points.map (Limits.pullback.snd f h) ξ = ofOver.pointsEquiv T t' ∧
            FiniteType.QuasiFiniteAt h (ofOver.pointsEquiv T t) ∧
            ξ ∈ relativeAssassin (Limits.pullback.snd f h)
              ((pullback (Limits.pullback.fst f h)).obj F) ∧
            ofOver.pointsEquiv T t ∉
              Points.map (Limits.pullback.snd f h) '' closure {ξ}) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
