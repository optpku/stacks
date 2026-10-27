/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.TensorPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

/-!
# Associated points of tensor products with pullbacks

For a relatively flat quasi-coherent module, the associated locus of its tensor
with a pulled-back quasi-coherent module is the intersection of its relative
associated locus with the inverse image of the associated locus on the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

namespace relativeAssassin

/-- For a morphism of locally Noetherian algebraic spaces with locally
Noetherian fibres and a relatively flat quasi-coherent module, the associated
points of its tensor with a pulled-back quasi-coherent module are precisely its
relative associated points mapping to associated points of the target module. -/
theorem associatedPoints_tensor_pullback_eq_inter_preimage
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hflat : flatOver F f)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyNoetherianFibers f] :
    associatedPoints (tensorPullback F f G) =
      relativeAssassin f F ∩ Points.map f ⁻¹' associatedPoints G :=
  sorry

/-- A point of `|X|` is associated to `tensorPullback F f G` if and only if it
lies in the relative assassin of `F` over `Y` and its image is associated to
`G`. -/
theorem mem_associatedPoints_tensor_pullback_iff
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hflat : flatOver F f)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyNoetherianFibers f] (x : Points X) :
    x ∈ associatedPoints (tensorPullback F f G) ↔
      x ∈ relativeAssassin f F ∧ Points.map f x ∈ associatedPoints G :=
  sorry

end relativeAssassin

end AlgebraicGeometry.AlgebraicSpace.Modules
