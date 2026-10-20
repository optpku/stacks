/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Weakly associated points under pushforward

The weakly associated locus of the pushforward of a quasi-coherent module along
a quasi-compact and quasi-separated morphism of algebraic spaces lies in the
image of the morphism.

The weakly associated locus of the pushforward of a quasi-coherent module along
an affine morphism of algebraic spaces lies in the image of its weakly associated locus.
If the source is locally Noetherian, these loci are equal.
For finite morphisms, these loci are equal without a Noetherian hypothesis.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A point outside the image of a quasi-compact and quasi-separated morphism of
algebraic spaces is not weakly associated to the pushforward of a quasi-coherent
module. -/
@[stacks 0CUQ]
theorem not_mem_weakAss_pushforward_of_not_mem_range
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent]
    (y : Points Y) (hy : y ∉ Set.range (Points.map f)) :
    y ∉ ((pushforward f).obj F).weakAss :=
  sorry

/-- The weakly associated locus of the pushforward of a quasi-coherent module
along a quasi-compact and quasi-separated morphism of algebraic spaces is
contained in the image of the morphism. -/
theorem weakAss_pushforward_subset_range
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] :
    ((pushforward f).obj F).weakAss ⊆ Set.range (Points.map f) :=
  sorry

/-- The weakly associated locus of the pushforward of a quasi-coherent module along
an affine morphism of algebraic spaces is contained in the image of the weakly
associated locus of that module. -/
theorem weakAss_pushforward_subset_image_of_affine
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((pushforward f).obj F).weakAss ⊆ Points.map f '' F.weakAss :=
  sorry

/-- A point of the target that is weakly associated to the affine pushforward of a
quasi-coherent module is the image of a weakly associated point of that module. -/
theorem mem_weakAss_pushforward_subset_of_affine
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
    (F : X.Modules) [F.IsQuasicoherent] (y : Points Y) :
    y ∈ ((pushforward f).obj F).weakAss →
      ∃ x : Points X, x ∈ F.weakAss ∧ Points.map f x = y := by
  intro hy
  exact weakAss_pushforward_subset_image_of_affine f F hy

/-- The weakly associated locus of the pushforward of a quasi-coherent module along
an affine morphism from a locally Noetherian algebraic space is the image of the
weakly associated locus of that module. -/
@[stacks 0CU8]
theorem weakAss_pushforward_eq_image_of_affine
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
    (F : X.Modules) [F.IsQuasicoherent] [IsLocallyNoetherian X] :
    ((pushforward f).obj F).weakAss = Points.map f '' F.weakAss :=
  sorry

/-- A point of the target is weakly associated to the affine pushforward of a
quasi-coherent module from a locally Noetherian algebraic space if and only if
it is the image of a weakly associated point of that module. -/
theorem mem_weakAss_pushforward_iff
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
    (F : X.Modules) [F.IsQuasicoherent] [IsLocallyNoetherian X] (y : Points Y) :
    y ∈ ((pushforward f).obj F).weakAss ↔
      ∃ x : Points X, x ∈ F.weakAss ∧ Points.map f x = y := by
  rw [weakAss_pushforward_eq_image_of_affine f F]
  rfl

/-- The weakly associated locus of the pushforward of a quasi-coherent module along
a finite morphism of algebraic spaces is the image of the weakly associated locus
of that module. -/
@[stacks 0CU9]
theorem weakAss_pushforward_eq_image_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((pushforward f).obj F).weakAss = Points.map f '' F.weakAss :=
  sorry

/-- A point of the target is weakly associated to the finite pushforward of a
quasi-coherent module if and only if it is the image of a weakly associated
point of that module. -/
theorem mem_weakAss_pushforward_iff_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    (F : X.Modules) [F.IsQuasicoherent] (y : Points Y) :
    y ∈ ((pushforward f).obj F).weakAss ↔
      ∃ x : Points X, x ∈ F.weakAss ∧ Points.map f x = y := by
  rw [weakAss_pushforward_eq_image_of_isFinite f F]
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
