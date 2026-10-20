module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Pushforward
import StacksCheckRecall

/-!
# Lemma 71.2.10

A point of `|Y|` outside the image of a quasi-compact quasi-separated morphism
of algebraic spaces is not weakly associated to the pushforward of a
quasi-coherent module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

/- Lemma 71.2.10: Let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces over `S`. Let `F` be a
quasi-coherent `𝒪_X`-module. Let `y ∈ Points Y` be a point which is not in the
image of `Points.map f`. Then `y` is not weakly associated to
`(pushforward f).obj F`. -/
@[stacks 0CUQ]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.not_mem_weakAss_pushforward_of_not_mem_range :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent]
      (y : Points Y), y ∉ Set.range (Points.map f) →
      y ∉ ((pushforward f).obj F).weakAss)

/- The weakly associated locus of the pushforward of a quasi-coherent module
along a quasi-compact quasi-separated morphism of algebraic spaces is contained
in the range of `Points.map f`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.weakAss_pushforward_subset_range :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent],
      ((pushforward f).obj F).weakAss ⊆ Set.range (Points.map f))
