module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap67.Lemma_67_48_6_Reduced

/-!
# Generic flatness for algebraic spaces, reduced case

This module records the simultaneous generic-flatness conditions for a morphism of
algebraic spaces and a module sheaf, together with the existence theorem over a
reduced base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- An open subspace `W ⊂ Y` is a generic-flatness locus for `f : X ⟶ Y` and
`ℱ : X.Modules` when the base change along `W.ι` is flat, locally of finite
presentation, and quasi-compact, while the restricted module is flat over `W`
and of finite presentation. -/
def GenericFlatnessOn (f : X ⟶ Y) (ℱ : X.Modules) (W : OpenSubspace Y) : Prop :=
  Flat (Limits.pullback.snd f W.ι) ∧
    LocallyOfFinitePresentation (Limits.pullback.snd f W.ι) ∧
    QuasiCompact (Limits.pullback.snd f W.ι) ∧
    flatOver ((pullback (Limits.pullback.fst f W.ι)).obj ℱ)
      (Limits.pullback.snd f W.ι) ∧
    ((pullback (Limits.pullback.fst f W.ι)).obj ℱ).IsFinitePresentation

/-- The generic-flatness predicate is equivalent to the five conditions on the
base-changed morphism and restricted module. -/
theorem genericFlatnessOn_iff (f : X ⟶ Y) (ℱ : X.Modules) (W : OpenSubspace Y) :
    GenericFlatnessOn f ℱ W ↔
      Flat (Limits.pullback.snd f W.ι) ∧
        LocallyOfFinitePresentation (Limits.pullback.snd f W.ι) ∧
        QuasiCompact (Limits.pullback.snd f W.ι) ∧
        flatOver ((pullback (Limits.pullback.fst f W.ι)).obj ℱ)
          (Limits.pullback.snd f W.ι) ∧
        ((pullback (Limits.pullback.fst f W.ι)).obj ℱ).IsFinitePresentation :=
  sorry

/-- A finite-type morphism to a reduced algebraic space and a finite-type
quasicoherent module admit a dense open subspace on which the base change is
flat, locally of finite presentation, and quasi-compact, and the restricted
module is flat over the open and of finite presentation. -/
theorem exists_dense_open_genericFlatness_of_reduced
    (f : X ⟶ Y) [IsReduced Y] [FiniteType f] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] :
    ∃ W : OpenSubspace Y,
      Dense (W.pointsSet : Set (Points Y)) ∧ GenericFlatnessOn f ℱ W :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
