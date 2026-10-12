/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Proposition_67_32_1_GenericFlatness
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation

/-!
# Generic flatness for algebraic spaces, reduced quasi-separated case

This module records the simultaneous generic-flatness conditions of finite
presentation for a morphism of algebraic spaces and a module sheaf, together
with the existence theorem over a reduced base when the morphism is
quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- An open subspace `W ⊂ Y` is a finite-presentation generic-flatness locus
for `f : X ⟶ Y` and `ℱ : X.Modules` when the base change along `W.ι` is flat
and of finite presentation, while the restricted module is flat over `W` and
of finite presentation. -/
def GenericFlatnessFinitePresentationOn (f : X ⟶ Y) (ℱ : X.Modules)
    (W : OpenSubspace Y) : Prop :=
  Flat (Limits.pullback.snd f W.ι) ∧
    FinitePresentation (Limits.pullback.snd f W.ι) ∧
    flatOver ((pullback (Limits.pullback.fst f W.ι)).obj ℱ)
      (Limits.pullback.snd f W.ι) ∧
    ((pullback (Limits.pullback.fst f W.ι)).obj ℱ).IsFinitePresentation

/-- The finite-presentation generic-flatness predicate is equivalent to the
four conditions on the base-changed morphism and restricted module. -/
theorem genericFlatnessFinitePresentationOn_iff (f : X ⟶ Y) (ℱ : X.Modules)
    (W : OpenSubspace Y) :
    GenericFlatnessFinitePresentationOn f ℱ W ↔
      Flat (Limits.pullback.snd f W.ι) ∧
        FinitePresentation (Limits.pullback.snd f W.ι) ∧
        flatOver ((pullback (Limits.pullback.fst f W.ι)).obj ℱ)
          (Limits.pullback.snd f W.ι) ∧
        ((pullback (Limits.pullback.fst f W.ι)).obj ℱ).IsFinitePresentation :=
  sorry

/-- Finite-presentation generic flatness is equivalent to generic flatness
together with quasi-separatedness of the base change. -/
theorem genericFlatnessFinitePresentationOn_iff_genericFlatnessOn
    (f : X ⟶ Y) (ℱ : X.Modules) (W : OpenSubspace Y) :
    GenericFlatnessFinitePresentationOn f ℱ W ↔
      GenericFlatnessOn f ℱ W ∧ QuasiSeparated (Limits.pullback.snd f W.ι) :=
  sorry

/-- A quasi-separated finite-type morphism to a reduced algebraic space and a
finite-type quasicoherent module admit a dense open subspace on which the
base change is flat and of finite presentation, and the restricted module is
flat over the open and of finite presentation. -/
theorem exists_dense_open_genericFlatness_of_reduced_quasiSeparated
    (f : X ⟶ Y) [IsReduced Y] [QuasiSeparated f] [FiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] :
    ∃ W : OpenSubspace Y, Dense (W.pointsSet : Set (Points Y)) ∧
      GenericFlatnessFinitePresentationOn f ℱ W :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
