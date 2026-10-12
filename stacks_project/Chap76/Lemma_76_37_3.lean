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
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Extending relative-dimension bounds from a dense open

A relative-dimension bound for a flat morphism of algebraic spaces locally of
finite type extends from a topologically dense open of the target when the
morphism is locally of finite presentation or the open inclusion is
quasi-compact.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeDimensionLE

/-- Lemma 76.37.3: a flat morphism of algebraic spaces locally of finite type
has relative dimension at most `d` if it has that bound after base change to a
topologically dense open subspace, and either the morphism is locally of finite
presentation or the open inclusion is quasi-compact. -/
@[stacks 0878]
theorem of_restrict_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f] (V : OpenSubspace Y) (d : ℕ)
    (hV_dense : Dense V.pointsSet)
    [RelativeDimensionLE (pullback.snd f V.ι) d]
    (h_finitePresentation_or_quasiCompact :
      LocallyOfFinitePresentation f ∨ QuasiCompact V.ι) :
    RelativeDimensionLE f d :=
  sorry

/-- A flat morphism of algebraic spaces locally of finite type and locally of
finite presentation has relative dimension at most `d` if it has that bound
after base change to a topologically dense open subspace. -/
theorem of_restrict_of_flat_of_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f]
    [LocallyOfFiniteType f] [LocallyOfFinitePresentation f]
    (V : OpenSubspace Y) (d : ℕ) (hV_dense : Dense V.pointsSet)
    [RelativeDimensionLE (pullback.snd f V.ι) d] :
    RelativeDimensionLE f d :=
  sorry

/-- A flat morphism of algebraic spaces locally of finite type has relative
dimension at most `d` if it has that bound after base change to a
quasi-compact topologically dense open subspace. -/
theorem of_restrict_of_flat_of_quasiCompact {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f]
    (V : OpenSubspace Y) (d : ℕ) (hV_dense : Dense V.pointsSet)
    [RelativeDimensionLE (pullback.snd f V.ι) d] [QuasiCompact V.ι] :
    RelativeDimensionLE f d :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeDimensionLE
