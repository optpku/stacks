/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced

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
