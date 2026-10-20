module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Pushforward

/-!
# Lemma 71.3.3

The weakly associated locus of a quasi-coherent module is preserved by
pushforward along a finite morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

/- Lemma 71.3.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a finite morphism of
algebraic spaces over `S`. Let `F` be a quasi-coherent `𝒪_X`-module. Then
`((pushforward f).obj F).weakAss = Points.map f '' F.weakAss`. -/
@[stacks 0CU9] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.weakAss_pushforward_eq_image_of_isFinite :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
      (F : X.Modules) [F.IsQuasicoherent],
      ((pushforward f).obj F).weakAss = Points.map f '' F.weakAss)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_weakAss_pushforward_iff_of_isFinite :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    (F : X.Modules) [F.IsQuasicoherent] (y : Points Y),
    y ∈ ((pushforward f).obj F).weakAss ↔
      ∃ x : Points X, x ∈ F.weakAss ∧ Points.map f x = y)
