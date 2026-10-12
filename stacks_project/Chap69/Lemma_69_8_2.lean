/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»

/-!
# Lemma 69.8.2

Positive-degree higher direct images of quasi-coherent modules vanish along
affine morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- Lemma 69.8.2: let `S` be a scheme. Let `f : X ⟶ Y` be an affine morphism of algebraic
spaces over `S`. Then `R^i f_* F = 0` for `i > 0` and any quasi-coherent `𝒪_X`-module `F`. -/
@[stacks 073H]
theorem higherDirectImage_isZero_of_affine
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) (hi : 0 < i) :
    IsZero (higherDirectImage f F i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
