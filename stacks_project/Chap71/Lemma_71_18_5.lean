/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap71.Definition_71_17_1_Blowup
public import stacks_project.Chap71.Definition_71_18_1_StrictTransform

/-!
# Affine pushforward of strict transforms of modules on algebraic spaces

Pushforward along the base change of an affine morphism of algebraic spaces
carries the strict transform of a quasi-coherent module to the strict
transform of its pushforward.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism `X ×_B B' ⟶ Y ×_B B'` induced by base change of a morphism
over the same algebraic space. -/
abbrev strictTransformBaseChangeMap {S : Scheme.{u}}
    {B B' X Y : AlgebraicSpace S} (b : B' ⟶ B) (g : X ⟶ Y) (y : Y ⟶ B) :
    strictTransformAmbient b (g ≫ y) ⟶ strictTransformAmbient b y :=
  ((Over.pullback b).map (Over.homMk g : Over.mk (g ≫ y) ⟶ Over.mk y)).left

namespace Modules

/-- Lemma 71.18.5: Let `S` be a scheme. Let `B` be an algebraic space over `S`.
Let `Z ⊂ B` be a closed subspace. Let `b : B' ⟶ B` be the blowing up of `Z`
in `B`. Let `g : X ⟶ Y` be an affine morphism of spaces over `B`. Let `F` be
a quasi-coherent sheaf on `X`. Let `g' : X ×_B B' ⟶ Y ×_B B'` be the base
change of `g`. Let `F'` be the strict transform of `F` relative to `b`. Then
`g'_* F'` is the strict transform of `g_* F`. -/
@[stacks 0866]
theorem pushforward_strictTransformModule_isomorphic_of_affine
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    (Z : ClosedSubspace B) [IsQuasiCoherent Z.idealSheaf]
    (πB : Blowup.along Z) (g : X ⟶ Y) (y : Y ⟶ B) [Affine g]
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIsomorphic
      ((pushforward (strictTransformBaseChangeMap πB.hom g y)).obj
        (strictTransformModule πB.hom (Z.inverseImage πB.hom) (g ≫ y) F))
      (strictTransformModule πB.hom (Z.inverseImage πB.hom) y
        ((pushforward g).obj F)) :=
  sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace
