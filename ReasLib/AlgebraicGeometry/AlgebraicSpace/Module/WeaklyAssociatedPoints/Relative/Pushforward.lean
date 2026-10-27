/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative.Locus
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative weak assassin under finite pushforward

Finite pushforward carries the relative weak assassin of a quasi-coherent
module on an algebraic space exactly to its image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Finite pushforward carries the relative weak assassin of a quasi-coherent
module exactly to its image under the map of points of algebraic spaces. -/
@[stacks 0CV4]
theorem relativeWeakAss_pushforward_eq_image_of_isFinite
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (i : Z ⟶ X)
    [IsFinite i] (G : Z.Modules) [G.IsQuasicoherent] :
    relativeWeakAss f ((pushforward i).obj G) =
      Points.map i '' relativeWeakAss (i ≫ f) G :=
  sorry

/-- A point of `|X|` is relatively weakly associated to the finite pushforward of
a quasi-coherent module if and only if it is the image of a point relatively
weakly associated to that module over `Y`. -/
theorem mem_relativeWeakAss_pushforward_iff_of_isFinite
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (i : Z ⟶ X)
    [IsFinite i] (G : Z.Modules) [G.IsQuasicoherent] (x : Points X) :
    x ∈ relativeWeakAss f ((pushforward i).obj G) ↔
      ∃ z : Points Z, z ∈ relativeWeakAss (i ≫ f) G ∧ Points.map i z = x := by
  rw [relativeWeakAss_pushforward_eq_image_of_isFinite f i G]
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
