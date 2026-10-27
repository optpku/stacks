/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.TensorPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

/-!
# Weakly associated points of a tensor with pullback

For a locally finite-type morphism of algebraic spaces, a finite-type
quasi-coherent module that is flat at a point over the target, and a
quasi-coherent module on the target, the point is weakly associated to the
tensor with pullback exactly when it belongs to the relative assassin and
its image is weakly associated to the base module. If flatness holds at
every point, the weakly associated locus is the relative assassin intersected
with the preimage of the weakly associated locus of the base module.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a locally finite-type morphism of algebraic spaces `f : X ⟶ Y`, a
finite-type quasi-coherent module `F` on `X` flat over `Y` at `x`, and a
quasi-coherent module `G` on `Y`, the point `x` is weakly associated to
`F ⊗ f^* G` if and only if its image is weakly associated to `G` and it
belongs to the relative assassin of `F`. -/
@[stacks 0CVK]
theorem mem_weakAss_tensorPullback_iff_of_flatOverAt
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (G : Y.Modules) [G.IsQuasicoherent] (x : Points X)
    (h_flat : flatOverAt F f x) :
    x ∈ (tensorPullback F f G).weakAss ↔
      Points.map f x ∈ G.weakAss ∧ x ∈ relativeAssassin f F :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces `f : X ⟶ Y`, a
finite-type quasi-coherent module `F` on `X` flat over `Y`, and a quasi-coherent
module `G` on `Y`, the weakly associated locus of `F ⊗ f^* G` equals the
intersection of the relative assassin of `F` with the inverse image of the
weakly associated locus of `G`. -/
@[stacks 0CVL]
theorem weakAss_tensorPullback_eq_inter_preimage
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (G : Y.Modules) [G.IsQuasicoherent]
    (h_flat : ∀ x : Points X, flatOverAt F f x) :
    (tensorPullback F f G).weakAss =
      relativeAssassin f F ∩ Points.map f ⁻¹' G.weakAss :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces `f : X ⟶ Y`, a
finite-type quasi-coherent module `F` on `X` flat over `Y`, and a quasi-coherent
module `G` on `Y`, a point is weakly associated to `F ⊗ f^* G` if and only if
it belongs to the relative assassin of `F` and its image is weakly associated
to `G`. -/
theorem mem_weakAss_tensorPullback_iff_of_flatOver
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (G : Y.Modules) [G.IsQuasicoherent]
    (h_flat : ∀ x : Points X, flatOverAt F f x) (x : Points X) :
    x ∈ (tensorPullback F f G).weakAss ↔
      x ∈ relativeAssassin f F ∧ Points.map f x ∈ G.weakAss :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
