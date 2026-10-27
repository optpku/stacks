/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative.TensorPullback
import StacksCheckRecall

/-!
# Weakly associated points of a tensor with pullback

For a locally finite-type morphism of algebraic spaces, a finite-type
quasi-coherent module that is flat over the target, and a quasi-coherent
module on the target, the weakly associated locus of the tensor with
pullback is the relative assassin intersected with the preimage of the
weakly associated locus of the base module.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.4.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type. Let `F` be a
finite type quasi-coherent `𝒪_X`-module which is flat over `Y`. Let `G` be
a quasi-coherent `𝒪_Y`-module. Then
`(tensorPullback F f G).weakAss = relativeAssassin f F ∩ Points.map f ⁻¹' G.weakAss`.
Under locally of finite type, `Ass_{X/Y}(F)` is `relativeAssassin f F`,
`tensorPullback F f G` is `F ⊗ f^* G`, and `|f|⁻¹` is `Points.map f ⁻¹'`.
`F` is flat over `Y` when it is flat over `Y` at every point of `|X|`. -/
@[stacks 0CVL] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.weakAss_tensorPullback_eq_inter_preimage :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (G : Y.Modules) [G.IsQuasicoherent]
      (h_flat : ∀ x : Points X, flatOverAt F f x),
    (tensorPullback F f G).weakAss =
      relativeAssassin f F ∩ Points.map f ⁻¹' G.weakAss)

/- A point of `|X|` lies in `(tensorPullback F f G).weakAss` if and only if
it lies in `relativeAssassin f F` and its image lies in `G.weakAss`, when
`F` is flat over `Y` at every point. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.mem_weakAss_tensorPullback_iff_of_flatOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (G : Y.Modules) [G.IsQuasicoherent]
      (h_flat : ∀ x : Points X, flatOverAt F f x) (x : Points X),
    x ∈ (tensorPullback F f G).weakAss ↔
      x ∈ relativeAssassin f F ∧ Points.map f x ∈ G.weakAss)

end AlgebraicGeometry.AlgebraicSpace.Modules
