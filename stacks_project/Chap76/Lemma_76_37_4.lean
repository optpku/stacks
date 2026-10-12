/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Extending finiteness from a dense open

A flat proper morphism of algebraic spaces is finite if it is finite after
base change to a topologically dense open subspace, and either the morphism
is locally of finite presentation or the open inclusion is quasi-compact.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFinite

/-- Lemma 76.37.4: a flat proper morphism of algebraic spaces is finite if it
is finite after base change to a topologically dense open subspace, and either
the morphism is locally of finite presentation or the open inclusion is
quasi-compact. -/
@[stacks 0B4J]
theorem of_restrict_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [Proper f] (V : OpenSubspace Y)
    (hV_dense : Dense V.pointsSet) [IsFinite (pullback.snd f V.ι)]
    (h_finitePresentation_or_quasiCompact :
      LocallyOfFinitePresentation f ∨ QuasiCompact V.ι) :
    IsFinite f :=
  sorry

/-- A flat proper morphism of algebraic spaces locally of finite presentation
is finite if it is finite after base change to a topologically dense open
subspace. -/
theorem of_restrict_of_flat_of_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] [Proper f]
    [LocallyOfFinitePresentation f] (V : OpenSubspace Y)
    (hV_dense : Dense V.pointsSet) [IsFinite (pullback.snd f V.ι)] :
    IsFinite f :=
  sorry

/-- A flat proper morphism of algebraic spaces is finite if it is finite after
base change to a quasi-compact topologically dense open subspace. -/
theorem of_restrict_of_flat_of_quasiCompact {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] [Proper f]
    (V : OpenSubspace Y) (hV_dense : Dense V.pointsSet)
    [IsFinite (pullback.snd f V.ι)] [QuasiCompact V.ι] :
    IsFinite f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsFinite
