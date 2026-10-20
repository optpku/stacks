/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Affine pushforward of strict transforms

Pushforward along the base change of an affine morphism of algebraic spaces
commutes with strict transforms of quasi-coherent module sheaves under blowup.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a blowup in a closed subspace, pushforward along the base change of an
affine morphism carries the strict transform of a quasi-coherent module to an
object isomorphic to the strict transform of its pushforward. -/
theorem pushforward_strictTransformModule_isomorphic_of_affine
    {S : Scheme.{u}} {B B' X Y : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z]
    (g : X ⟶ Y) (y : Y ⟶ B) [Affine g]
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIsomorphic
      ((pushforward (AlgebraicGeometry.AlgebraicSpace.overBaseChange g y b)).obj
        (strictTransformModule b (Z.inverseImageSubspace b) (g ≫ y) F))
      (strictTransformModule b (Z.inverseImageSubspace b) y
        ((pushforward g).obj F)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
